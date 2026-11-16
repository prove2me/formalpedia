-- Prove2me | Theorems.Thm_SmoothedNash_Supplement_theorem_4_17
-- name    : SmoothedNash.Supplement.theorem_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:11:14.864579+00:00
-- url     : https://prove2.me/theorems/effd04b8-e924-4f05-a3ed-f84030e582a3
-- title:
--   Theorem 4.17 — smoothed case: Algorithm 4 finds an $\varepsilon$-VI solution w.p. $\ge 1-p$ in runtime $\max\{C^n P_v n^{-n/2} a^{n+1}/(p\varepsilon),\ C^n P_d P_v n^{-3n/2} a^{3n-2}(a+L_2)^2/p^2\}$
-- statement:
--   Let $n \ge 2$, $0 < \varepsilon < 1$, and let $F$ be a random map satisfying, for every realization, Assumptions 1.8, 1.9, 1.10 with constants $L_0, L_1, L_2$ (with $a = L_0 + L_1 \ge 1$), and the density Assumptions 1.6 and 1.7 with constants $P_v$ and $P_d$ (the Setting of Theorem 1.14).
--
--   **Theorem.** There is a universal constant $C$ such that for all $0 < p < 1$ the following algorithm finds an $\varepsilon$-approximate solution to the variational inequality for $F$ with probability at least $1 - p$: Algorithm 4 with inputs $L_0, L_1, L_2$, accuracy $\varepsilon$ and the row-gap bound $\theta$ of Lemma 4.2. Its runtime is at most the maximum of
--   $$
--   C^n \frac{P_v}{n^{n/2}} (L_0 + L_1)^{n+1} p^{-1} \varepsilon^{-1}
--   \qquad\text{and}\qquad
--   C^n \frac{P_d}{n^n} \frac{P_v}{n^{n/2}} (L_0 + L_1)^{3n-2} (L_0 + L_1 + L_2)^2 p^{-2} .
--   $$
--   Precisely: there is a universal $C_\theta > 1$ (the constant of Lemma 4.2, defining $\theta$) and, for each exponent $\kappa$ of the per-iteration arithmetic, a universal $C$, such that with probability at least $1-p$ a terminated run exists, every run has runtime at most the maximum above, and every terminated run outputs an $\varepsilon$-approximate VI solution.
--
--   This is the smoothed guarantee for the homotopy method (informal Theorem 1.14): the first explicit runtime bound for approximate fixed points of general smooth maps by a homotopy-type method.
--
--   **Formalization Note** The probability bound is stated as: the outer measure of the failure set is at most $p$. $n^{n/2}$ is $(\sqrt n)^n$. The algorithm is deterministic; the randomness is the draw of $F$.
--
--   Differences from the source:
--
--   - reading: there exists an algorithm → Algorithm 4 with inputs L0, L1, L2, accuracy ε and θ = theta417 Cθ (Lemma 4.2), with ∃ Cθ > 1 quantified before every other parameter; reason: the algorithm of the proof; a bare existential over algorithms would be trivially witnessed
--   - reading: for all 0 < p < 1, there exists a universal constant C → ∃ C (for each κ) before p and every other parameter; reason: a universal constant does not depend on p; the proof's C does not
--   - reading: a = L0 + L1; without loss of generality a ≥ 1 (§4.1.1, p.26) → hypothesis 1 ≤ L0 + L1; reason: the standing assumption of Section 4
--   - reading: in a runtime → alg4Runtime κ = (calls + N + 1)(n+1)^κ bounded for every run, ∀ κ ∃ C; reason: the cost model of Theorem 4.5 with an unspecified polynomial per iteration
--   - reading: finds an ε-approximate solution with probability at least 1 − p → P(failure) ≤ p, where success = a terminated run exists ∧ every run's runtime ≤ the bound ∧ every terminated run's output is an ε-approximate VI solution; reason: the full success event of a run of the algorithm
--   - encoding: probability at least 1 − p → outer measure of the failure set ≤ p; reason: no measurability of the event is needed; on a measurable event it is the same
--   - encoding: densities bounded by Pv and Pd (Assumptions 1.6, 1.7) → measure inequalities P[F(x) ∈ S] ≤ Pv λ_n(S), P[(F(x), J_F(x)^⊤ v) ∈ S] ≤ Pd λ_{2n}(S) and the same for J_F(x) v; reason: equivalent formulation; v^⊤ J_F(x) is the vector J_F(x)^⊤ v
--   - encoding: random F → ω ↦ F ω x measurable for every x; reason: the random map is a random variable at each point
--   - encoding: n^{n/2} → (√n)^n; reason: equal
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 4.17, p.41 (Setting of Theorem 1.14, p.6; Lemma 4.2, p.26)

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_IsApproxVI
import Definitions.Def_SmoothedNash_Supplement_BoundedNorm
import Definitions.Def_SmoothedNash_Supplement_LipschitzOnBall
import Definitions.Def_SmoothedNash_Supplement_JacobianLipschitz
import Definitions.Def_SmoothedNash_Supplement_ValueDensityBound
import Definitions.Def_SmoothedNash_Supplement_JointDensityBound
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Trace
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Terminated
import Definitions.Def_SmoothedNash_Supplement_alg4Out
import Definitions.Def_SmoothedNash_Supplement_alg4Runtime
import Definitions.Def_SmoothedNash_Supplement_theta417
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Theorem 4.17 (Smoothed-case algorithm)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.41). For the Setting of Theorem 1.14,
for all `0 < p < 1`, there exists a universal constant `C` such that there exists an algorithm that
finds an `ε`-approximate solution to a variational inequality with probability at least `1 − p` in a
runtime that is the maximum of the two following terms
`C^n (Pv/n^{n/2}) (L0 + L1)^{n+1} p^{−1} ε^{−1}` and
`C^n (Pd/n^n) (Pv/n^{n/2}) (L0 + L1)^{3n−2} (L0 + L1 + L2)^2 p^{−2}`.

The Setting of Theorem 1.14 (p.6): Assumptions 1.6, 1.7, 1.8, 1.9, 1.10, 1.11, `0 < ε < 1`, `n ≥ 2`.
The algorithm is Algorithm 4 run on `F` with inputs `L0, L1, L2`, accuracy `ε`, and
`θ = Cθ^{−n} (a^{2n} Pd/n^n)^{−1} p / L_J` (Lemma 4.2; `theta417`). Stated: there is a universal
`Cθ > 1`, and for every cost exponent `κ` a universal `C > 0`, such that for every random `F` in this
setting the probability that the following fails is at most `p`: a terminated run exists, every run has
running time at most the maximum of the two terms, and every terminated run outputs an
`ε`-approximate VI solution for `F`.

**Formalization Note** Assumptions 1.8–1.10 hold for every realization; 1.6 and 1.7 are the density
bounds. "There exists an algorithm" is stated for the paper's algorithm, with its constant `Cθ`
quantified before every other parameter, so the statement is not a bare existential over functions.
"For all `p` there exists a universal `C`" is read as one `C` for all `p` (a universal constant).
`a = L0 + L1 ≥ 1` is the standing "without loss of generality" of §4.1.1 (p.26). `n^{n/2}` is
`(√n)^n`. The running time is `alg4Runtime κ`; `C` depends only on `κ`. The failure probability is
the outer measure of the failure set. -/
theorem theorem_4_17 :
    ∃ Cθ : ℝ, 1 < Cθ ∧ ∀ κ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n → ∀ (ε p L0 L1 L2 Pv Pd : ℝ), 0 < ε → ε < 1 → 0 < p → p < 1 →
        1 ≤ L0 + L1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (F : Ω → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        (∀ x, Measurable fun ω => F ω x) →
        (∀ ω, BoundedNorm (F ω) L0) → (∀ ω, LipschitzOnBall (F ω) L1) →
        (∀ ω, JacobianLipschitz (F ω) L2) →
        ValueDensityBound P F Pv → JointDensityBound P F Pd →
        P {ω | ¬ ((∃ q v N, IsAlg4Terminated (F ω) L0 L1 L2 ε (theta417 Cθ n L0 L1 L2 Pd p) q v N) ∧
            (∀ q v N, IsAlg4Trace (F ω) L0 L1 L2 ε (theta417 Cθ n L0 L1 L2 Pd p) q v N →
              alg4Runtime κ (F ω) ε N ≤
                max (C ^ n * (Pv / Real.sqrt n ^ n) * (L0 + L1) ^ (n + 1) * p⁻¹ * ε⁻¹)
                  (C ^ n * (Pd / (n : ℝ) ^ n) * (Pv / Real.sqrt n ^ n) * (L0 + L1) ^ (3 * n - 2) *
                    (L0 + L1 + L2) ^ 2 * (p ^ 2)⁻¹)) ∧
            (∀ q v N, IsAlg4Terminated (F ω) L0 L1 L2 ε (theta417 Cθ n L0 L1 L2 Pd p) q v N →
              IsApproxVI (F ω) ε (alg4Out (F ω) L0 L1 ε q N)))} ≤ ENNReal.ofReal p := by sorry

end SmoothedNash.Supplement
