-- Prove2me | Theorems.Thm_ThreeBoundConditional_row_destroying_cover
-- name    : ThreeBoundConditional.row_destroying_cover
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:42:36.712924+00:00
-- url     : https://prove2.me/theorems/505efb68-3e7b-4d99-8d1f-a647b976b322
-- title:
--   Destroying one ordinary row has a target-or-guard classification
-- statement:
--   Let \(F\) be nested with \(t_i\le t_j\), \(g_j\le g_i\), and \(q\le q_i\). Suppose row \(v\) accepts at \((t_j,g_j,q)\). If flipping \(((w,c),a)\) makes that row false at \((t_i,g_i,q_i)\), then either its own target child is destroyed, or the flip activates a selected outgoing guard:
--   \[
--   R(v,w),\quad \ell(v,w)=c,\quad
--   F_{g_j}(x_{w,c})=\mathrm{false},\quad
--   F_{g_i}(x_{w,c}^{\{a\}})=\mathrm{true}.
--   \]
--   This is the row-level form of the destructive-flip cover.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ConditionalOrdinary, lines 476–529; source SHA256 f3399d34ca31ad9b4ad9de5a4ab294181bbd230bb91c7ec217c0414e4e592080.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

theorem ThreeBoundConditional.row_destroying_cover (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (hF : Nested F) (ti tj gi gj : L)
    (ht : ti ≤ tj) (hg : gj ≤ gi) (qi q : ℕ) (hq : q ≤ qi)
    (x : ((V × Bool) × I) → Bool) (v : V) (hv : ordinaryRow S F tj gj q x v)
    (w : V) (c : Bool) (a : I)
    (hoff : ordinaryRowBool S F ti gi qi v (flip x {((w,c),a)}) = false) :
    (w = v ∧ F ti (flip (child x v c) {a}) = false) ∨
      (S.Adj v w ∧ S.label v w = c ∧ F gj (child x w c) = false ∧
        F gi (flip (child x w c) {a}) = true) := by sorry
