-- Prove2me | Theorems.Thm_P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be
-- name    : P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:15.712213+00:00
-- url     : https://prove2.me/theorems/1632548e-040b-4e07-a06f-72da103499e3
-- title:
--   P2 M Formalism LT LTL norm finsum le  8658a123f7be: P2 M Formalism LT LTL norm finsum le  8658a123f7be
-- statement:
--   The P2 M Formalism LT LTL norm finsum le  8658a123f7be construction uses the P2 M Formalism LT LTL norm finsum le  8658a123f7be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L188-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L188-L195

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by sorry

alias «Formalism».«LT».«LTL».«norm_finsum_le'» := P2M_Formalism_LT_LTL_norm_finsum_le__8658a123f7be
