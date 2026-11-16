-- Prove2me | Theorems.Thm_SmoothedNash_Supplement_theorem_3_3
-- name    : SmoothedNash.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:09:32.167584+00:00
-- url     : https://prove2.me/theorems/36fe2ac3-db39-46ea-8bcf-56684a3c89b3
-- title:
--   Theorem 3.3 — Algorithm 3 finds an $\varepsilon$-approximate fixed point with $\le (135(1+L_1))^n P_v \mathrm{Vol}(B_n)\lceil\log_2\frac{1+L_1}{\varepsilon}\rceil$ expected evaluations
-- statement:
--   Let $B_n$ be the closed Euclidean unit ball of $\mathbb R^n$, $L_1 \ge 0$ and $0 < \varepsilon \le 1$, and let $K = \lceil \log_2((1 + L_1)/\varepsilon) \rceil$. Algorithm 3 builds the sets $D_0 = \{0\}, D_1, \dots, D_K$ of grid points by tree search and pruning and outputs any point of $D_K$.
--
--   **Theorem.**
--
--   1. *(Correctness, for every map.)* If $F : B_n \to B_n$ is $L_1$-Lipschitz, then $D_K$ is nonempty and every point $x \in D_K$ satisfies $\|F(x) - x\| \le \varepsilon$.
--   2. *(Expected evaluations.)* If $F$ is random, maps $B_n$ into itself and is $L_1$-Lipschitz for every realization, and satisfies Assumption 1.6 with density bound $P_v$, then the expected number of evaluations of $F$ is at most
--   $$
--   (135(1 + L_1))^n \cdot P_v \cdot \mathrm{Vol}(B_n) \cdot \Bigl\lceil \log_2 \frac{1 + L_1}{\varepsilon} \Bigr\rceil .
--   $$
--   3. *(Expected running time.)* For every exponent $\kappa$ of the per-candidate overhead there is an absolute constant $C$ such that, under the same hypotheses, the expected running time in the cost model of Remark 3.5 is at most $C^n$ times this bound.
--
--   This is the cover-based fixed-point guarantee of the paper (informal Theorem 1.13): under smoothed analysis, recursive brute force pays only $C^n \cdot \log(1/\varepsilon)$ evaluations in expectation, against the $(1/\varepsilon)^n$ of a plain grid search.
--
--   **Formalization Note** The map is a function on all of $\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`); only its values on the ball are used. Points of $D_K$ are stored as integer vectors. The expectation is the lower Lebesgue integral, and $\mathrm{Vol}(B_n)$ is the Lebesgue measure of the closed unit ball.
--
--   Differences from the source:
--
--   - reading: the algorithm finds an approximate fixed point (Output: any point in D_K) → D_K is nonempty and every point of D_K is an ε-approximate fixed point, for every L1-Lipschitz F : B → B; reason: the output may be any point of D_K, so the guarantee must hold for all of them; it holds for every realization, as the proof shows
--   - generalization: correctness under Assumptions 1.9 and 1.6 for a random F → correctness (clause 1) for every deterministic L1-Lipschitz F : B → B, without the density assumption; reason: the guarantee holds for every realization (the proof uses only Brouwer and Lipschitzness), so it specializes to every realization of the paper's random F
--   - reading: number of evaluations of F → Σ_{k=1}^{K} Σ_{x ∈ D_{k−1}} |C(x,k)|, one per (parent, candidate) pair; reason: the count the proof bounds; it dominates the number of distinct evaluations, so this is the stronger reading
--   - reading: expected running time at most C^n times this bound, for an absolute constant C (Remark 3.5) → ∀ κ ∃ C > 0 with E[alg3Time κ] ≤ C^n · bound, in the cost model of Remark 3.5 (prefix enumeration of C(x,k) plus (n+1)^κ per candidate); reason: Remark 3.5 leaves the poly(n) per insertion unspecified; quantifying over every exponent covers every polynomial
--   - encoding: F : B(0,1) → B(0,1) → F : ℝ^n → ℝ^n with Set.MapsTo F (closedBall 0 1) (closedBall 0 1); reason: values outside the ball are never used
--   - encoding: density of F(x) at most Pv → P[F(x) ∈ S] ≤ Pv · λ_n(S) for every Borel S; reason: equivalent formulation of a density bound
--   - encoding: L1-Lipschitz; F a random map → 0 ≤ L1; ω ↦ F ω x measurable for every x; reason: Lipschitz constants are nonnegative; the random map is a random variable at each point
--   - encoding: grid C_k = {x ∈ B(0,1) : x_i √n / r_k ∈ ℤ} → integer vectors j with x = (2^k √n)⁻¹ j; reason: the same points; a level-(k−1) vector i is the level-k vector 2i
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 3.3, pp.21–22 (Algorithm 3, p.21; Remark 3.5, p.23)

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_IsApproxFixedPoint
import Definitions.Def_SmoothedNash_Supplement_LipschitzOnBall
import Definitions.Def_SmoothedNash_Supplement_ValueDensityBound
import Definitions.Def_SmoothedNash_Supplement_latticePt
import Definitions.Def_SmoothedNash_Supplement_alg3Level
import Definitions.Def_SmoothedNash_Supplement_alg3Depth
import Definitions.Def_SmoothedNash_Supplement_alg3Evals
import Definitions.Def_SmoothedNash_Supplement_alg3Time
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Theorem 3.3** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), pp.21–22). Suppose we perform Algorithm 3. Let `0 < ε ≤ 1`.
Then, for a function `F : B(0,1) → B(0,1)` satisfying Assumptions 1.9 and 1.6, the algorithm finds an
approximate fixed point that satisfies `‖F(x) − x‖ ≤ ε` using an expected number of evaluations of `F`
at most `(135(1 + L1))^n · Pv · Vol(B_n) · ⌈log₂((1 + L1)/ε)⌉`, where `Vol(B_n)` is the volume of an
`n`-dimensional ball. Its expected running time is at most `C^n` times this bound, for an absolute
constant `C` (Remark 3.5).

The conjunction states, with `K = ⌈log₂((1 + L1)/ε)⌉` (`alg3Depth`):
1. correctness, for every `F` (every realization): if `F` maps `B(0,1)` into itself and is
   `L1`-Lipschitz on it, then `D_K` is nonempty and every point of `D_K` (the output is "any point
   in `D_K`") is an `ε`-approximate fixed point;
2. expected evaluations: for a random `F` that, for every realization, maps the ball into itself and
   is `L1`-Lipschitz, and satisfies Assumption 1.6 with bound `Pv`,
   `E[#evaluations] ≤ (135(1 + L1))^n · Pv · Vol(B_n) · K`;
3. expected running time: for every cost exponent `κ` there is `C > 0` such that, under the same
   hypotheses, `E[running time] ≤ C^n · (135(1 + L1))^n · Pv · Vol(B_n) · K`.

**Formalization Note** The points of `D_K` are stored as integer vectors `j` and the point is
`latticePt n K j`. The running time is `alg3Time κ`, the cost model of Remark 3.5 with per-candidate
overhead `(n + 1)^κ`; `C` depends only on `κ`. `Vol(B_n)` is `volume (closedBall 0 1)` in
`EuclideanSpace ℝ (Fin n)`. The expectation is the lower Lebesgue integral. -/
theorem theorem_3_3 :
    (∀ {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (L1 ε : ℝ),
      0 ≤ L1 → 0 < ε → ε ≤ 1 →
      Set.MapsTo F (Metric.closedBall 0 1) (Metric.closedBall 0 1) → LipschitzOnBall F L1 →
      (alg3Level F L1 (alg3Depth L1 ε)).Nonempty ∧
        ∀ j ∈ alg3Level F L1 (alg3Depth L1 ε),
          IsApproxFixedPoint F ε (latticePt n (alg3Depth L1 ε) j)) ∧
    (∀ {n : ℕ} (L1 ε Pv : ℝ), 0 ≤ L1 → 0 < ε → ε ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (F : Ω → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ x, Measurable fun ω => F ω x) →
        (∀ ω, Set.MapsTo (F ω) (Metric.closedBall 0 1) (Metric.closedBall 0 1)) →
        (∀ ω, LipschitzOnBall (F ω) L1) → ValueDensityBound P F Pv →
        ∫⁻ ω, (alg3Evals (F ω) L1 ε : ENNReal) ∂P ≤
          ENNReal.ofReal ((135 * (1 + L1)) ^ n * Pv * (alg3Depth L1 ε : ℝ)) *
            volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) ∧
    (∀ κ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (L1 ε Pv : ℝ), 0 ≤ L1 → 0 < ε → ε ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (F : Ω → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ x, Measurable fun ω => F ω x) →
        (∀ ω, Set.MapsTo (F ω) (Metric.closedBall 0 1) (Metric.closedBall 0 1)) →
        (∀ ω, LipschitzOnBall (F ω) L1) → ValueDensityBound P F Pv →
        ∫⁻ ω, (alg3Time κ (F ω) L1 ε : ENNReal) ∂P ≤
          ENNReal.ofReal (C ^ n * ((135 * (1 + L1)) ^ n * Pv * (alg3Depth L1 ε : ℝ))) *
            volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by sorry

end SmoothedNash.Supplement
