-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_unionExpr_bound
-- name    : Sensitivity213981Formal.ThreeBoundNumeric.unionExpr_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:32:57.644375+00:00
-- url     : https://prove2.me/theorems/6b94de86-61ac-4faf-bc0a-68f7406eafca
-- title:
--   Adjacent boundary maxima control a nonadjacent union profile
-- statement:
--   Let \(v\) upper-bound the profiles of a Boolean family \(F\) indexed by \(\operatorname{Fin}(n)\). If \(i\le j<k\le l\), then
--   \[
--   D_F(i,j,k,l)\le \operatorname{unionExpr}(n,i,j,k,l)[v].
--   \]
--   Here the right-hand side is the maximum of the stored \(D\)-coordinates obtained by placing an adjacent true-to-false boundary between \(j\) and \(k\), while retaining endpoints \(i,l\). This supplies the interval union bounds used in shared-child repair costs.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ProfileIntervals.lean, lines 81–95.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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

theorem Sensitivity213981Formal.ThreeBoundNumeric.unionExpr_bound :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v) (i j k l : Fin n)
  (hij : @LE.le.{0} (Fin n) (@instLEFin n) i j) (hjk : @LT.lt.{0} (Fin n) (@instLTFin n) j k)
  (hkl : @LE.le.{0} (Fin n) (@instLEFin n) k l),
  @Sensitivity213981Formal.ThreeBoundProfiles.DBound (Fin n) I inst F i j k l
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundNumeric.unionExpr n (@Fin.val n i) (@Fin.val n j) (@Fin.val n k)
        (@Fin.val n l))) := by sorry
