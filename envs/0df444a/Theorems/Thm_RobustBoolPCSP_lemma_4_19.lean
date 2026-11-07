-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_19
-- name    : RobustBoolPCSP.lemma_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:01.15745+00:00
-- url     : https://prove2.me/theorems/67b07c54-3f16-4eb2-b4a7-bf171e3a6588
-- title:
--   Lemma 4.19 (Replacement) — simulating lists preserve perfect integrality gaps
-- statement:
--   Let $(P^*,Q^*)$ be a relation pair of arity $\ell$, and suppose a fixed finite list of signed $\Gamma$-constraints on the literals $y_1,\dots,y_\ell$ satisfies: every tuple of $P^*$ strongly satisfies every constraint of the list, and every tuple that weakly satisfies all constraints of the list lies in $Q^*$. Let $I$ be a signed instance of a template $\Gamma'$ containing $(P^*,Q^*)$. If $I$ is a perfect integrality gap, then the instance obtained by replacing each $(P^*,Q^*)$-constraint by the list, with its literals substituted for $y_1,\dots,y_\ell$, is a perfect integrality gap.
--
--   The replacement keeps all variables and introduces none; it transports the canonical gaps of Theorem 4.9 to any mixed symmetric template.
--
--   Differences from the source:
--   - reading: replacing yields a perfect integrality gap (template unnamed) → the replaced instance is a perfect integrality gap of the union template Γ ∪ Γ′; reason: the replaced instance uses the list's Γ-pairs and the remaining pairs of Γ′
--   - encoding: the pair (P*, Q*) of a template containing it → the pair j★ of Γ′; reason: naming the pair by its index
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.19, p.26

import Mathlib
import Definitions.Def_RobustBoolPCSP_SDP
import Definitions.Def_RobustBoolPCSP_Simulation

set_option autoImplicit false

namespace RobustBoolPCSP

/-- **Lemma 4.19 (Replacement)**, p.26. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let (P∗, Q∗) be a relation pair of arity ℓ, and suppose that a fixed finite list of signed
Γ-constraints on the literals y1, . . . , yℓ satisfies: every tuple of P∗ strongly satisfies every
constraint of the list, and every tuple that weakly satisfies all constraints of the list lies in
Q∗. If a signed instance of a template containing (P∗, Q∗) is a perfect integrality gap, then
replacing each (P∗, Q∗)-constraint by the list, with its literals substituted for y1, . . . , yℓ,
yields a perfect integrality gap."

**Formalization Note.** The template containing `(P∗, Q∗)` is `Γ'` with `(P∗, Q∗) = (P'_{j★},
Q'_{j★})`; the replaced instance `replaceInst j★ L I` keeps the variables and the other
constraints and is a signed instance of the union template `Γ ∪ Γ'`. -/
theorem lemma_4_19 {ι ι' : Type} [DecidableEq ι'] (Γ : Template ι Bool Bool)
    (Γ' : Template ι' Bool Bool) (jstar : ι')
    (L : List (Σ j : ι, Fin (Γ.r j) → Literal (Γ'.r jstar)))
    (hL : IsSimulatingList Γ (Γ'.P jstar) (Γ'.Q jstar) L)
    (I : SignedInstance Γ') (hI : IsPerfectGap I) :
    IsPerfectGap (replaceInst jstar L I) := by sorry

end RobustBoolPCSP
