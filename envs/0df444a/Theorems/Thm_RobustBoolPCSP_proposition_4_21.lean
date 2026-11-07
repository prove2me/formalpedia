-- Prove2me | Theorems.Thm_RobustBoolPCSP_proposition_4_21
-- name    : RobustBoolPCSP.proposition_4_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:33.023129+00:00
-- url     : https://prove2.me/theorems/586ea10d-c55f-445d-83be-ac70d924780f
-- title:
--   Proposition 4.21 (Majority and the mode property)
-- statement:
--   Let $(P,Q)$ be a Boolean relation pair of arity $r$ and take the identity output map, so that $W=Q$. Then
--
--   $$(P,Q)\ \text{has the mode property}\iff \mathrm{Maj}_L\ \text{preserves}\ (P,Q)\ \text{for every odd } L\ge1.$$
--
--   With Lemma 4.1 this turns the Majority case of the dichotomy into an instance of the log-free robust algorithm (Theorem 2.4).
--
--   Differences from the source:
--   - encoding: the mode property of Definition 2.3 with the identity output map → ModeProperty P {x | id ∘ x ∈ Q}, the probability-vector form of Definition 2.3; reason: Definition 2.3 states the two forms as equivalent; W = (id^r)⁻¹(Q)
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Proposition 4.21, p.27

import Mathlib
import Definitions.Def_RobustBoolPCSP_ModeProperty
import Definitions.Def_SymBoolPCSP_CFixing_Basic

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Proposition 4.21 (Majority and the mode property)**, p.27. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"For a Boolean relation pair (P, Q) and the identity output map, (P, Q) has the mode property of
Definition 2.3 if and only if every odd-arity Majority operation preserves (P, Q)."

**Formalization Note.** With the identity output map `h = id`, `W = (h^r)⁻¹(Q) = Q`. Odd arities
include `L = 1`. -/
theorem proposition_4_21 {r : ℕ} (P Q : Set (Fin r → Bool)) :
    ModeProperty P {x | (id : Bool → Bool) ∘ x ∈ Q} ↔ ∀ L : ℕ, Odd L → PolOf P Q (Maj L) := by sorry

end RobustBoolPCSP
