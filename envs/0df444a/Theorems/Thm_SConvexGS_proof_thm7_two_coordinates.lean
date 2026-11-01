-- Prove2me | Theorems.Thm_SConvexGS_proof_thm7_two_coordinates
-- name    : SConvexGS.proof_thm7_two_coordinates
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:54.600589+00:00
-- url     : https://prove2.me/theorems/5018f033-6694-4d8b-a5a3-fc2a25c84ec2
-- title:
--   Proof of Theorem 7, pp.22–23 (corrected: $f$ concave) — the supermodular inequality for two coordinates in $\operatorname{int}(\operatorname{dom}f_*)$
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be an upper semicontinuous concave proper GS-function. Let $z\in\mathbb R^n$, let $i\ne j$ and $\alpha,\beta>0$, and suppose that $a=z+\alpha\mathbf e_i$ and $b=z+\beta\mathbf e_j$ lie in $\operatorname{int}(\operatorname{dom}f_*)$. Then
--
--   $$f_*(a)+f_*(b)\le f_*(z)+f_*(z+\alpha\mathbf e_i+\beta\mathbf e_j).$$
--
--   Here $z=a\wedge b$ and $z+\alpha\mathbf e_i+\beta\mathbf e_j=a\vee b$. By the reduction the paper cites from Topkis (1998, Corollary 2.6.1), the case of two coordinates carries the proof of Theorem 7 on the interior of the domain.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: f concave → ConcaveOn of toReal ∘ f on dom f (IsConcaveFn); reason: ConcaveOn needs a module target; with f < ∞ this is concavity of the extended-valued f
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - correction: usc proper GS-function, with no concavity → adds IsConcaveFn f; reason: the printed step is false: n = 2, S = {0} ∪ {(2k, k+1), (k+1, 2k) : k ≥ 1}, f = 0 at 0, −1 on the rest of S, −∞ off S, is usc and proper GS (proved in Solutions/verification/SConvexGS_Sanity4.lean); dom f₍*₎ = {p : 2p₁ + p₂ ≥ 0, p₁ + 2p₂ ≥ 0}; with z = (−1, −1), i = 1, j = 2, α = β = 4, a = (3, −1) and b = (−1, 3) lie in int(dom f₍*₎), f₍*₎(a) = f₍*₎(b) = 0 and f₍*₎(z) = −∞, so 0 > −∞ = f₍*₎(z) + f₍*₎(z + αe₁ + βe₂)
--   - encoding: a = a ∧ b + αeᵢ, b = a ∧ b + βeⱼ, 1 ≤ i < j ≤ n → a = z + αeᵢ, b = z + βeⱼ, i ≠ j; reason: a ∧ b = z, and the condition is symmetric in the two coordinates
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 7, pp.22–23

import Mathlib
import Definitions.Def_SConvexGS_IsConcaveFn
import Definitions.Def_SConvexGS_IsProperGS
import Definitions.Def_SConvexGS_concaveConj

namespace SConvexGS

/-- Proof of Theorem 7, pp.22–23 (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29)):
for a usc concave proper GS-function `f` and `a, b ∈ int(dom f₍*₎)` with only two different
coordinates, `a = z + αeᵢ` and `b = z + βeⱼ` with `i ≠ j` and `α, β > 0`,
`f₍*₎(a) + f₍*₎(b) ≤ f₍*₎(z) + f₍*₎(z + αeᵢ + βeⱼ)`.

Formalization Note: `z = a ∧ b` and `z + αeᵢ + βeⱼ = a ∨ b`. `i ≠ j` covers the paper's `i < j` by
symmetry. Concavity is the correction made to Theorem 7. -/
theorem proof_thm7_two_coordinates {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_concave : IsConcaveFn f)
    (hf_gs : IsProperGS f) (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (ha : z + α • (Pi.single i 1 : Fin n → ℝ) ∈ interior (dom (concaveConj f)))
    (hb : z + β • (Pi.single j 1 : Fin n → ℝ) ∈ interior (dom (concaveConj f))) :
    concaveConj f (z + α • (Pi.single i 1 : Fin n → ℝ)) +
        concaveConj f (z + β • (Pi.single j 1 : Fin n → ℝ)) ≤
      concaveConj f z +
        concaveConj f (z + α • (Pi.single i 1 : Fin n → ℝ) +
          β • (Pi.single j 1 : Fin n → ℝ)) := by sorry

end SConvexGS
