-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_intw_ph
-- name    : PositivityTheory.ThKR.LL.intw_ph
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:25.619948+00:00
-- url     : https://prove2.me/theorems/90ebae6e-cb35-4fa5-bb3b-dc88bba2d146
-- title:
--   LL: intw ph
-- statement:
--   The LL construction uses the intw ph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L79-L87

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.intw_ph {S : Eu l →L[ℝ] Eu l} (hS : ∀ x y, ⟪x, S y⟫ = ⟪y, S x⟫) (p q : Eu l) : Intw (ph S) p q p (q + S p) := by sorry
