-- Prove2me | Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_restrict_pow
-- name    : PositivityTheory.HtPt.KtwS.exists_restrict_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:56.769403+00:00
-- url     : https://prove2.me/theorems/e9c7d7a7-a8c3-4066-a032-371b9c8e8cf2
-- title:
--   Ktw S: exists restrict pow
-- statement:
--   The Ktw S construction uses the exists restrict pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/ExistsLineBundleTwistMulOf.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HodgeTatePoints/ExistsLineBundleTwistMulOf.lean#L34-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem PositivityTheory.HtPt.KtwS.exists_restrict_pow (hLT : LineTwist.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y)
    (M : LineBundle S x) (M' : LineBundle S y) (r : Ω → K')
    (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'), Q.toSubSystem = M.toSubSystem.pow n ∧
      Q'.toSubSystem = M'.toSubSystem.pow n ∧ RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by sorry
