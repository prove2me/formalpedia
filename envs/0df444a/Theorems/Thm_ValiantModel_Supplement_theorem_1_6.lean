-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_1_6
-- name    : ValiantModel.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:23:35.779676+00:00
-- url     : https://prove2.me/theorems/054a1d51-65c0-4224-9326-31a09955c12a
-- title:
--   Theorem 1.6, p.6 — halfspaces in $\mathbb R^d$ are learnable in Valiant's model (corrected: $\log(2/\delta)$)
-- statement:
--   There is an absolute constant $C>0$ such that for every dimension $d\ge1$ there is an algorithm that learns the class of halfspaces in $\mathbb R^d$ in Valiant's model (Definition 3) using $m(\varepsilon,\delta)$ positive examples and $q(\varepsilon,\delta)$ membership queries, where for all $\varepsilon,\delta\in(0,1)$
--   $$m(\varepsilon,\delta)\le C\,\frac{d^2\log_2 d\cdot\log_2(1/\varepsilon)+\log_2(2/\delta)}{\varepsilon},\qquad q(\varepsilon,\delta)\le C\,d^3\log_2^3 d\cdot\log_2\frac{1}{\varepsilon\delta}.$$
--
--   Halfspaces in $\mathbb R^d$, $d\ge2$, are not learnable from positive examples alone, so this is a case where membership queries change which classes are learnable.
--
--   Differences from the source:
--   - correction: log(1/δ) in m(ε, δ) → log₂(2/δ); reason: the printed bound tends to 0 as ε, δ → 1 (and as δ → 1 for every ε when d = 1), forcing no examples and no queries, which fails: with halfspaces {x₁ ≥ c}, c ∈ ℕ, and D_c the point mass at c·e₁, success on (h_c, D_c) requires c·e₁ ∈ supp g ⊆ h_c, these events are disjoint in c, so a learner without information succeeds with probability inf_c P(event c) = 0 < 1 − δ; log₂(2/δ) = 1 + log₂(1/δ) agrees up to the constant for δ ≤ 1/2
--   - reading: log1/εδ → log₂(1/(ε δ)); reason: Lemma 5.13 confirms the product reading
--   - encoding: O(·) → one absolute constant `C > 0` quantified before d; the learner and budgets may depend on d; reason: the proofs' constants are uniform in d
--   - encoding: log → `Real.logb 2`; reason: logarithms are base two (§3, p.14)
--   - encoding: ℝ^d with every distribution → `Fin d → ℝ` with its Borel σ-algebra and every Borel probability measure; compatibility almost surely, the error by the outer measure; reason: the standard measurable structure of ℝ^d; continuous distributions included
--   - encoding: halfspaces {x : ⟨n, x⟩ ≥ c}, n ≠ 0 → the published `IsHalfspace` sets {x : a ⬝ᵥ x ≤ β}, a ≠ 0; reason: the two families coincide with a = −n, β = −c
--   - encoding: a randomized learner → `RandProtocol`: an arbitrary probability space of internal randomness and a deterministic `GProtocol` for each value, success probability by the lower Lebesgue integral; reason: this is exact whenever the success event is measurable, and the paper's probability is defined only then; examples and queries interleave, queries may be asked anywhere, and outputs are improper
--   - encoding: m(ε, δ) positive examples and q(ε, δ) membership queries → `GHasComplexity (halfspaceClass d) L m q`: at most m and q calls on every path for every value of the randomness; reason: separate budgets per oracle, as stated
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem 1.6, p.6 (PDF p.8); restated p.37 (PDF p.39); proof §5.5, pp.38–43 (PDF pp.40–45)

import Mathlib
import Definitions.Def_ValiantModel_Supplement_GeneralModel
import Definitions.Def_ValiantModel_Supplement_Halfspaces

namespace ValiantModel.Supplement

/-- **Theorem 1.6 (Halfspaces Are Learnable on `ℝ^d`)**, Hanneke, Mehrotra, Velegkas, Zampetakis,
arXiv:2605.13840 (version held, sha256 f793f255…), p.6 (PDF p.8), restated p.37 (PDF p.39): there is
an algorithm that learns halfspaces in `ℝ^d` in Valiant's model (Definition 3) using `m(ε, δ)` positive
examples and `q(ε, δ)` membership queries, with
`m(ε, δ) ≤ C (d² log d · log(1/ε) + log(2/δ)) / ε` and `q(ε, δ) ≤ C d³ log³ d · log(1/(εδ))`.

**Formalization Note.** `O(·)` is one absolute constant `C`, the same for every dimension `d ≥ 1`;
the learner may depend on `d`. Logarithms are base two. Corrected: the printed `log(1/δ)` is
`log(2/δ)` here; the printed sample bound tends to `0` as `ε, δ → 1` while no learner without examples
succeeds (halfspaces `{x₁ ≥ c}`, `c ∈ ℕ`, with point masses at `c e₁`). `ℝ^d` is `Fin d → ℝ` with its
Borel σ-algebra, and every Borel probability measure is a distribution. -/
theorem theorem_1_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d →
      ∃ (L : ℝ → ℝ → RandProtocol (Fin d → ℝ)) (m q : ℝ → ℝ → ℕ),
        GHasComplexity (halfspaceClass d) L m q ∧
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          (m ε δ : ℝ) ≤ C * ((d : ℝ) ^ 2 * Real.logb 2 d * Real.logb 2 (1 / ε) +
            Real.logb 2 (2 / δ)) / ε ∧
          (q ε δ : ℝ) ≤ C * (d : ℝ) ^ 3 * Real.logb 2 d ^ 3 * Real.logb 2 (1 / (ε * δ)) := by sorry

end ValiantModel.Supplement
