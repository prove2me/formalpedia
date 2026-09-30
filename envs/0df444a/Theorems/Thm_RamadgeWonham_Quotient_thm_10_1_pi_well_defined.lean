-- Prove2me | Theorems.Thm_RamadgeWonham_Quotient_thm_10_1_pi_well_defined
-- name    : RamadgeWonham.Quotient.thm_10_1_pi_well_defined
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:45:06.241573+00:00
-- url     : https://prove2.me/theorems/ff6c83a7-3b96-4391-97e4-0e8443973ca4
-- title:
--   Proof of Theorem 10.1, p. 223 — the map π: X⁰ → X is well defined
-- statement:
--   Let $\mathcal G$ be a trim generator over a finite alphabet $\Sigma$, and let $\mathcal S = (S, \phi)$, $S = (X, \Sigma, \xi, x_0, X_m)$, be a complete supervisor for $\mathcal G$ with $S$ accessible. Put $K_3 := L(\mathcal S/\mathcal G)$ and assume that $S$ is $K_3$-reduced and $K_3$-trim. Let $\hat S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0)$ be a trim recognizer for $K_3$ in which every state is marked. Then for all $s, t \in K_3$,
--   $$\xi^0(s, x^0_0) = \xi^0(t, x^0_0) \implies \xi(s, x_0) = \xi(t, x_0).$$
--
--   Hence $\pi(x^0) := \xi(s, x_0)$, for any $s \in K_3$ with $\xi^0(s, x^0_0) = x^0$, defines a map $\pi : X^0 \to X$; this is the first step of the proof of the quotient structure theorem.
--
--   **Formalization Note** $K_3$ is written out as the closed-loop language of $\mathcal S$. Both sides of each equation are optional states (`Option`); for $s, t \in K_3$ they are defined.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 223, proof of Theorem 10.1, second paragraph

import Mathlib
import Definitions.Def_RamadgeWonham_Quotient_Projection
import Definitions.Def_RamadgeWonham_Quotient_Reduced
import Definitions.Def_RamadgeWonham_Quotient_Recognizer

namespace RamadgeWonham.Quotient

open Shared.Generator

/-- Proof of Theorem 10.1 (p. 223, second paragraph): the map `π(x⁰) := ξ(s, x₀)` for
`s ∈ K₃` with `ξ⁰(s, x⁰₀) = x⁰` is well defined: if `s, t ∈ K₃` and `ξ⁰(s, x⁰₀) = ξ⁰(t, x⁰₀)`,
then `ξ(s, x₀) = ξ(t, x₀)`. -/
theorem thm_10_1_pi_well_defined
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮 : Shared.Complete 𝒢 𝒮)
    (hred : KReduced 𝒮.S (Shared.Lsup 𝒢 𝒮)) (htrim : KTrim 𝒮.S (Shared.Lsup 𝒢 𝒮))
    (R : Shared.Generator α) (hRrec : IsRecognizer R (Shared.Lsup 𝒢 𝒮)) (hRtrim : R.IsTrim)
    (hRQm : R.Qm = Set.univ) :
    ∀ s t : List α, s ∈ Shared.Lsup 𝒢 𝒮 → t ∈ Shared.Lsup 𝒢 𝒮 → R.run s = R.run t →
      𝒮.S.run s = 𝒮.S.run t := by sorry

end RamadgeWonham.Quotient
