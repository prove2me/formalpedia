-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_ClosureCertificate_rule_sound_two
-- name    : Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.rule_sound_two
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:53:12.162426+00:00
-- url     : https://prove2.me/theorems/db6fb05b-b928-4cce-9c2c-790659d8c9a3
-- title:
--   Every profile-closure inference preserves a valid Boolean bound
-- statement:
--   Let \(F\) be a nested Boolean family, and let \(r\) be one of the defined profile-closure rules. If natural numbers \(x,y\) give valid semantic bounds at the rule's two source coordinates, then
--   \[
--   \operatorname{Sem}(F,r.\mathrm{target},\operatorname{combine}_r(x,y))
--   \]
--   holds. The combination is \(x\) for one-source monotonicity rules, \(x+y\) for the union rule, and \(\max(x,y)\) for partition rules. This theorem makes a finite closure certificate a proof of profile bounds rather than a numerical heuristic.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ClosureCertificate.lean, lines 51–105.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.rule_sound_two :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (r : Sensitivity213981Formal.ThreeBoundFullProfile.Rule n) (x y : Nat)
  (hx :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
      (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.source₀ n r) x)
  (hy :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
      (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.source₁ n r) y),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
    (@Sensitivity213981Formal.ThreeBoundFullProfile.Rule.target n r)
    (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.combine n r x y) := by sorry
