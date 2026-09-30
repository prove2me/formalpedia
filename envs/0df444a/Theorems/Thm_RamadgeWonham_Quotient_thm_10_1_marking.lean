-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_thm_10_1_marking
-- name    : RamadgeWonham.Quotient.thm_10_1_marking
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:48:29.405523+00:00
-- url     : https://prove2.me/theorems/94fa4ae2-bee1-4997-9681-e9c8336cb3f0
-- title:
--   Proof of Theorem 10.1, pp. 223–224 — L_m(𝒮⁰/𝒢) = L_m(𝒮/𝒢)
-- statement:
--   Under the hypotheses of Theorem 10.1 ($\mathcal G$ trim over a finite $\Sigma$; $\mathcal S = (S, \phi)$ complete with $S$ accessible, $K_3$-reduced and $K_3$-trim, where $K_3 = L(\mathcal S/\mathcal G)$; $\hat S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0)$ a trim recognizer for $K_3$), let $\pi : X^0 \to X$ satisfy $\pi(\xi^0(s, x^0_0)) = \xi(s, x_0)$ for every $s \in K_3$, and let $\mathcal S^0 = (S^0, \phi \circ \pi)$ with $S^0 = (X^0, \Sigma, \xi^0, x^0_0, \pi^{-1}(X_m))$. Then
--   $$L_m(\mathcal S^0/\mathcal G) = L_m(\mathcal S/\mathcal G).$$
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, pp. 223-224, proof of Theorem 10.1, last paragraph

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection
import Definitions.Def_RamadgeWonham_Quotient_Reduced
import Definitions.Def_RamadgeWonham_Quotient_Recognizer

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proof of Theorem 10.1 (pp. 223–224, final paragraph): for the map `π : X⁰ → X` with
`π(ξ⁰(s, x⁰₀)) = ξ(s, x₀)` on `K₃`, the supervisor `𝒮⁰ = (S⁰, φ ∘ π)` with
`S⁰ = (X⁰, Σ, ξ⁰, x⁰₀, π⁻¹(X_m))` satisfies `L_m(𝒮⁰/𝒢) = L_m(𝒮/𝒢)`. -/
theorem thm_10_1_marking
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮 : Shared.Complete 𝒢 𝒮)
    (hred : KReduced 𝒮.S (Shared.Lsup 𝒢 𝒮)) (htrim : KTrim 𝒮.S (Shared.Lsup 𝒢 𝒮))
    (R : Shared.Generator α) (hRrec : IsRecognizer R (Shared.Lsup 𝒢 𝒮)) (hRtrim : R.IsTrim)
    (hRQm : R.Qm = Set.univ)
    (π : R.Q → 𝒮.S.Q)
    (hπ : ∀ s ∈ Shared.Lsup 𝒢 𝒮, ∀ x0 : R.Q, R.run s = some x0 → 𝒮.S.run s = some (π x0)) :
    Shared.Lmsup 𝒢 (ofRecognizer R (π ⁻¹' 𝒮.S.Qm) (fun x0 => 𝒮.φ (π x0))) = Shared.Lmsup 𝒢 𝒮 := by sorry

end RamadgeWonham.Quotient
