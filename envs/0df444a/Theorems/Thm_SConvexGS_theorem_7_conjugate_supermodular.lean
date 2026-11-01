-- Prove2me | Theorems.Thm_SConvexGS_theorem_7_conjugate_supermodular
-- name    : SConvexGS.theorem_7_conjugate_supermodular
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:02.915814+00:00
-- url     : https://prove2.me/theorems/ccae30a7-cce4-43ff-a8c0-8c4c54ca417e
-- title:
--   Theorem 7 (corrected: $f$ concave) — the concave conjugate of a usc concave proper GS-function is supermodular
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be an upper semicontinuous concave proper GS-function. Then its concave conjugate $f_*$ is supermodular:
--
--   $$f_*(a)+f_*(b)\le f_*(a\wedge b)+f_*(a\vee b)\qquad\text{for all }a,b\in\mathbb R^n.$$
--
--   This is the bridge from GS to S-concavity: the supermodularity of $f_*$ is what Theorem 3 converts back into the exchange property of $f$, which gives the implication from left to right in Corollary 2.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: f concave → ConcaveOn of toReal ∘ f on dom f (IsConcaveFn); reason: ConcaveOn needs a module target; with f < ∞ this is concavity of the extended-valued f
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - correction: usc proper GS-function, with no concavity → adds IsConcaveFn f; reason: the printed statement is false: n = 2, S = {0} ∪ {(2k, k+1), (k+1, 2k) : k ≥ 1}, f = 0 at 0, −1 on the rest of S, −∞ off S, is usc and proper GS, and with a = (2, −1), b = (−1, 2), f₍*₎(a) + f₍*₎(b) = 0 > −∞ = f₍*₎(a ∧ b) + f₍*₎(a ∨ b) (proved in Solutions/verification/SConvexGS_Sanity4.lean)
--   - encoding: f₍*₎(x) + f₍*₎(y) ≤ f₍*₎(x ∧ y) + f₍*₎(x ∨ y) → SupermodularEReal: g x + g y ≤ g (x ⊔ y) + g (x ⊓ y); reason: the published definition, the same inequality with the two right-hand terms swapped
--   - encoding: the conjugate, defined on p.14 for dom f ≠ ∅ → at f ≡ −∞ the def is +∞ and the inequality holds; reason: no hypothesis is needed for this undefined case
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Theorem 7, p.22

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SupermodularEReal
import Definitions.Def_SConvexGS_IsConcaveFn
import Definitions.Def_SConvexGS_IsProperGS
import Definitions.Def_SConvexGS_concaveConj

namespace SConvexGS

/-- **Theorem 7** (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), p.22),
corrected: if `f : ℝⁿ → [−∞, ∞)` is a usc concave proper GS-function, then its concave conjugate
`f₍*₎` is supermodular.

Formalization Note: the printed theorem omits concavity and is false without it (`paper.md`).
`SupermodularEReal g` is `g x + g y ≤ g (x ⊔ y) + g (x ⊓ y)`, the two terms on the right being in the
opposite order to p.9. At `f ≡ ⊥` the `def` gives `f₍*₎ ≡ ⊤`, and the inequality holds. -/
theorem theorem_7_conjugate_supermodular {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_concave : IsConcaveFn f)
    (hf_gs : IsProperGS f) :
    DiscreteConvex.ConjugacyDuality.SupermodularEReal (concaveConj f) := by sorry

end SConvexGS
