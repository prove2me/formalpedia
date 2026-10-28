-- Prove2me | Theorems.Thm_ThreeBoundNumeric_ClosureCertificate_rule_sound_two
-- name    : ThreeBoundNumeric.ClosureCertificate.rule_sound_two
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:43.639347+00:00
-- url     : https://prove2.me/theorems/791f1ad0-1c5a-408d-9310-dfa6fcb4111c
-- title:
--   Every profile-closure inference preserves a valid Boolean bound
-- statement:
--   Let \(F\) be a nested Boolean family, and let \(r\) be one of the defined profile-closure rules. If natural numbers \(x,y\) give valid semantic bounds at the rule's two source coordinates, then
--   \[
--   \operatorname{Sem}(F,r.\mathrm{target},\operatorname{combine}_r(x,y))
--   \]
--   holds. The combination is \(x\) for one-source monotonicity rules, \(x+y\) for the union rule, and \(\max(x,y)\) for partition rules. This theorem makes a finite closure certificate a proof of profile bounds rather than a numerical heuristic.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ClosureCertificate, lines 51–105; source SHA256 bc6b5758158196e25c384f9b6d527a2e020b577675a25c6d2a48edc187cf4af5.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ClosureCertificate
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures

namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundProfiles
end ThreeBoundProfiles
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundNumeric
end ThreeBoundNumeric
open ThreeBoundNumeric
namespace ThreeBoundNumeric.ClosureCertificate
end ThreeBoundNumeric.ClosureCertificate
open ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile
variable {n : ℕ}

theorem ThreeBoundNumeric.ClosureCertificate.rule_sound_two {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (r : Rule n)
    (x y : ℕ) (hx : Sem F (source₀ r) x) (hy : Sem F (source₁ r) y) :
    Sem F r.target (combine r x y) := by sorry
