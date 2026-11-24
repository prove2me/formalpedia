-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ArcConst_arc__C_injective_0a8b9ebdf4ed
-- name    : P2M_GlobalTheory_ArcConst_arc__C_injective_0a8b9ebdf4ed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:40.968956+00:00
-- url     : https://prove2.me/theorems/9926503e-e612-4d91-b84f-9f14000ca970
-- title:
--   P2 M Global Theory Arc Const arc  C injective 0a8b9ebdf4ed: P2 M Global Theory Arc Const arc  C injective 0a8b9ebdf4ed
-- statement:
--   The P2 M Global Theory Arc Const arc  C injective 0a8b9ebdf4ed construction uses the P2 M Global Theory Arc Const arc  C injective 0a8b9ebdf4ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L99-L102

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem P2M_GlobalTheory_ArcConst_arc__C_injective_0a8b9ebdf4ed (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective ((arcι Dw K).comp (PowerSeries.C (R := K))) := by sorry

alias «GlobalTheory».«ArcConst».«arcι_C_injective» := P2M_GlobalTheory_ArcConst_arc__C_injective_0a8b9ebdf4ed
