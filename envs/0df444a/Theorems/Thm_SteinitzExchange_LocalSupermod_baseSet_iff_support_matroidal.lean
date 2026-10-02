-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_baseSet_iff_support_matroidal
-- name    : SteinitzExchange.LocalSupermod.baseSet_iff_support_matroidal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:49:43.283125+00:00
-- url     : https://prove2.me/theorems/cd68ec80-bd51-4b25-aebf-af154ec33344
-- title:
--   Theorem 5.1 — (B1) holds iff the support function ψ° is "matroidal"
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a finite nonempty set with $B=\mathbb Z^V\cap\overline B$, i.e. every integer point of the convex hull of $B$ belongs to $B$. Let $\psi^\circ(p)=\min\{\langle p,x\rangle\mid x\in B\}$. Then
--
--   $$B\ \text{satisfies (B1)}\iff\psi^\circ\ \text{is "matroidal" (satisfies (C1) and (C2))}.$$
--
--   The theorem restates the exchange property of $B$ in terms of the support function of $\overline B$: supermodularity of $X\mapsto\psi^\circ(\chi_X)$ together with correctness of the greedy formula. It is the step that turns localizations into exchange properties in the Local Supermodularity Theorem.
--
--   **Formalization Note.** The hypothesis $B=\mathbb Z^V\cap\overline B$ is stated as: every $z\in\mathbb Z^V$ whose image lies in `hull B` belongs to $B$ (the reverse inclusion is automatic). It is a hypothesis of the paper and is not implied by finiteness. $\psi^\circ$ is positively homogeneous for every finite nonempty $B$; "matroidal" includes that property.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 291, Theorem 5.1 (with Eq. (5.1), p. 289)

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 291, Theorem 5.1. Let `B ⊆ ℤ^V` be finite, nonempty, with
`B = ℤ^V ∩ B̄` (every integer point of the convex hull of `B` lies in `B`). Then `B` satisfies
(B1) iff `ψ°(p) = min{⟨p, x⟩ | x ∈ B}` is "matroidal" (satisfies (C1) and (C2)). -/
theorem baseSet_iff_support_matroidal {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull B → z ∈ B) :
    IsIntegralBaseSet B ↔ IsMatroidal (supportMin B) := by sorry

end SteinitzExchange.LocalSupermod
