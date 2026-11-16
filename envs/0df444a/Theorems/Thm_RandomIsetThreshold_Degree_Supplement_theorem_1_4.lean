-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_Supplement_theorem_1_4
-- name    : RandomIsetThreshold.Degree.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:16:27.656321+00:00
-- url     : https://prove2.me/theorems/63607310-69a5-4678-9f86-fff211a7e869
-- title:
--   Theorem 1.4 — influence threshold for finding large independent sets
-- statement:
--   Fix an integer $r\ge2$ and $0<\varepsilon<r^{1/(r-1)}-1$. Let $H_{n,p}$ be the binomial $r$-uniform hypergraph, and write
--
--   $$L=\left(\frac{(r-2)!\log(n^{r-1}p)}{-\log(1-p)}\right)^{1/(r-1)}.$$
--
--   There are positive $d,\gamma_0$, depending only on $r,\varepsilon$, such that for every $0<\delta<1/2$ there are positive $c,\xi$ and an integer $n_0>0$, depending only on $r,\varepsilon,\delta$, with the following properties for every $n\ge n_0$ and $d/n^{r-1}\le p\le1-n^{-\xi}$.
--
--   For a real-vector random function $f(G,R)$, the seed $R$ has an arbitrary probability law independently of the graph. Its influence is
--
--   $$\mathcal I(f)=\frac12\sum_e\mathbb E\|f(H_{n,p},R)-f(H_{n,p}^{(e)},R)\|_2^2,$$
--
--   where only edge $e$ is independently resampled and both evaluations use the same seed. Success at tolerance $\gamma$ means that there exists an independent set $J$ with $|J|\ge(1+\varepsilon)L$ and $\|f(H_{n,p},R)-\mathbf1_J\|_2^2\le\gamma|J|$.
--
--   1. For every $0\le\gamma\le\gamma_0$ and every real budget $B>0$, every seedwise measurable $f$ satisfies
--
--      $$\mathcal I(f)\le B\le cpL^{r+1}\quad\Longrightarrow\quad\mathbb P(f\text{ succeeds at tolerance }\gamma)\le\delta.$$
--
--   2. There exists a deterministic real-vector function $h$, independently of the budget and tolerance, such that
--
--      $$\mathcal I(h)\le28pL^{r+1},\qquad\mathbb P(h\text{ succeeds at tolerance }0)\ge1-\delta/2.$$
--
--      Consequently, for every $B\ge28pL^{r+1}$ with $B>0$ and every $0\le\gamma\le\gamma_0$, this same function is admissible and succeeds with probability at least $1-\delta/2$. Zero tolerance forces equality with an actual independent-set indicator on the success event.
--
--   This companion theorem identifies the influence threshold for unrestricted random functions, alongside the mission's degree threshold. It imposes no polynomial degree, norm, square-integrability, bounded-output, finite-seed or running-time condition. The paper writes $O(\delta)$ in the threshold display; its proof yields error constant 1 in the lower branch and 1/2 in the upper branch, while retaining $C=28$. The exact witness therefore also satisfies the advertised success bound $1-\delta$.
--
--   **Formalization Note** The existing definitions supply extended nonnegative expectations, so a non-integrable squared displacement is never replaced by a zero Bochner integral. The theorem is a statement to be proved, not a claim that a proof has already been checked.
--
--   Differences from the source:
--   - generalization: O(δ) and 1 − O(δ) in (5), with the final witness success at least 1 − δ → success at most δ in the lower branch and at least 1 − δ/2 for the exact witness and the upper branch; reason: Theorem 1.5 and Remark 1.6 (p. 4) give the lower bound on failure, and (23) (p. 9) gives exact success at least 1 − δ/2; these explicit inequalities imply all printed probability claims with C = 28
--   - encoding: supremum over random functions with influence at most the positive real budget I → a universal inequality for every admissible random function, plus one deterministic witness admissible for every budget B ≥ 28pL^(r+1); reason: probabilities lie in [0,1] and the zero function makes each positive-budget class nonempty; the two clauses give exactly the two supremum bounds without a supremum over seed-space types
--   - encoding: vertices [n], Bernoulli-p edge indicators, and L from (1) → the published Fin n, unitInterval, graphLaw, scale and Regime definitions; reason: relabeling vertices and encoding a probability by its subtype change no instance; real powers retain the full exponent and bias interval
--   - encoding: arbitrary random functions with independent seed R and influence (4) → arbitrary measurable probability seed spaces, SeedMeasurable, product sampling, and extended nonnegative influence with one shared seed; reason: measurability is the standing probability convention; nonnegative expectations may be infinite without an integrability or norm hypothesis
--   - encoding: constants depending only on the listed parameters and all sufficiently large n → d and γ₀ are chosen before δ; c, ξ and positive natural n₀ before γ, n, p, B and the random function; the deterministic witness is chosen before γ and B; reason: quantifier order expresses the stated uniformity, and a natural cutoff is equivalent for the integer vertex count
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 3, Theorem 1.4 and Eq. (5); definitions pp. 2–3, Eqs. (1), (2), (4); explicit probability bounds p. 4, Theorem 1.5 and Remark 1.6, and p. 9, Eqs. (21)–(23).

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_Hypergraph
import Definitions.Def_RandomIsetThreshold_Degree_RandomOutput

open MeasureTheory

namespace RandomIsetThreshold.Degree.Supplement

/-- Theorem 1.4, with the explicit error bounds of Remark 1.6 and (23).
The witness is exact (gamma = 0) and is chosen independently of gamma and the budget. -/
theorem theorem_1_4 (r : ℕ) (hr : 2 ≤ r) (ε : ℝ)
    (hε : 0 < ε) (hεmax : ε < rootFactor r - 1) :
    ∃ d γ₀ : ℝ, 0 < d ∧ 0 < γ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ c ξ : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 0 < ξ ∧ 0 < n₀ ∧
          ∀ n : ℕ, n₀ ≤ n → ∀ p : unitInterval, Regime n r p d ξ →
            (∀ γ : ℝ, 0 ≤ γ → γ ≤ γ₀ →
              ∀ B : ℝ, 0 < B → B ≤ c * (p : ℝ) * (scale n r p) ^ (r + 1) →
                ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
                  [IsProbabilityMeasure μ] (f : Cube n r → Ω → Vector n),
                  SeedMeasurable f → influence p μ f ≤ ENNReal.ofReal B →
                    successProbability p μ f ε γ ≤ δ) ∧
            (∃ h : Cube n r → Vector n,
              detInfluence p h ≤ ENNReal.ofReal (28 * (p : ℝ) * (scale n r p) ^ (r + 1)) ∧
              1 - δ / 2 ≤ detSuccessProbability p h ε 0 ∧
              ∀ γ : ℝ, 0 ≤ γ → γ ≤ γ₀ → ∀ B : ℝ, 0 < B →
                28 * (p : ℝ) * (scale n r p) ^ (r + 1) ≤ B →
                  detInfluence p h ≤ ENNReal.ofReal B ∧
                  1 - δ / 2 ≤ detSuccessProbability p h ε γ) := by sorry

end RandomIsetThreshold.Degree.Supplement
