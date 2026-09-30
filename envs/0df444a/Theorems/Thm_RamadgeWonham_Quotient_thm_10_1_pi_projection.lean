-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_thm_10_1_pi_projection
-- name    : RamadgeWonham.Quotient.thm_10_1_pi_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:46:39.177033+00:00
-- url     : https://prove2.me/theorems/4d97d340-f74f-4f10-8718-1e1159b9f037
-- title:
--   Proof of Theorem 10.1, p. 223 — π is a projection 𝒮⁰ → 𝒮 with X⁰_m := π⁻¹(X_m), φ⁰ := φ∘π
-- statement:
--   Under the hypotheses of Theorem 10.1 ($\mathcal G$ trim over a finite $\Sigma$; $\mathcal S = (S, \phi)$ complete with $S$ accessible, $K_3$-reduced and $K_3$-trim, where $K_3 = L(\mathcal S/\mathcal G)$; $\hat S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0)$ a trim recognizer for $K_3$), there is a map $\pi : X^0 \to X$ with
--   $$\pi\big(\xi^0(s, x^0_0)\big) = \xi(s, x_0) \qquad \text{for all } s \in K_3,$$
--   and, with $X^0_m := \pi^{-1}(X_m)$ and $\phi^0 := \phi \circ \pi$, $\pi$ is a projection from $\mathcal S^0 = (S^0, \phi^0)$, $S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0_m)$, to $\mathcal S$.
--
--   This is part (ii) of the quotient structure theorem, and it fixes the marker set and feedback map of $\mathcal S^0$.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 223, proof of Theorem 10.1, first and third paragraphs

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection
import Definitions.Def_RamadgeWonham_Quotient_Reduced
import Definitions.Def_RamadgeWonham_Quotient_Recognizer

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proof of Theorem 10.1 (p. 223, third paragraph): there is a map `π : X⁰ → X` with
`π(ξ⁰(s, x⁰₀)) = ξ(s, x₀)` for every `s ∈ K₃`, and with `X⁰_m := π⁻¹(X_m)` and `φ⁰ := φ ∘ π` it is a
projection `π : 𝒮⁰ → 𝒮`. -/
theorem thm_10_1_pi_projection
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮 : Shared.Complete 𝒢 𝒮)
    (hred : KReduced 𝒮.S (Shared.Lsup 𝒢 𝒮)) (htrim : KTrim 𝒮.S (Shared.Lsup 𝒢 𝒮))
    (R : Shared.Generator α) (hRrec : IsRecognizer R (Shared.Lsup 𝒢 𝒮)) (hRtrim : R.IsTrim)
    (hRQm : R.Qm = Set.univ) :
    ∃ π : R.Q → 𝒮.S.Q,
      (∀ s ∈ Shared.Lsup 𝒢 𝒮, ∀ x0 : R.Q, R.run s = some x0 → 𝒮.S.run s = some (π x0)) ∧
      IsProjection (ofRecognizer R (π ⁻¹' 𝒮.S.Qm) (fun x0 => 𝒮.φ (π x0))) 𝒮 π := by sorry

end RamadgeWonham.Quotient
