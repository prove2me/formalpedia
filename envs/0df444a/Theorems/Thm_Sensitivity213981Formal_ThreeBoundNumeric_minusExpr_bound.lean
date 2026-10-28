-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_minusExpr_bound
-- name    : Sensitivity213981Formal.ThreeBoundNumeric.minusExpr_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:32:15.800167+00:00
-- url     : https://prove2.me/theorems/7ee0b031-3770-4aca-acfd-42186cd63f9c
-- title:
--   Adjacent boundary maxima control a nonadjacent mixed profile
-- statement:
--   Let \(F\) be a Boolean family indexed by \(\operatorname{Fin}(n)\), and let \(v\) upper-bound all of its stored profiles. For indices \(i\le j<k\), the mixed profile across the interval from \(j\) to \(k\) satisfies
--   \[
--   M_F(i,j,k)\le \operatorname{minusExpr}(n,i,j,k)[v].
--   \]
--   The expression on the right is the maximum of the stored adjacent-boundary \(M\)-coordinates over that interval. This permits transfers to use nonadjacent levels without storing every such profile separately.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ProfileIntervals.lean, lines 52–65.

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

theorem Sensitivity213981Formal.ThreeBoundNumeric.minusExpr_bound :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (hv : @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F v) (i j k : Fin n)
  (hij : @LE.le.{0} (Fin n) (@instLEFin n) i j) (hjk : @LT.lt.{0} (Fin n) (@instLTFin n) j k),
  @Sensitivity213981Formal.ThreeBoundProfiles.MBound (Fin n) I inst F i j k
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundNumeric.minusExpr n (@Fin.val n i) (@Fin.val n j) (@Fin.val n k))) := by sorry
