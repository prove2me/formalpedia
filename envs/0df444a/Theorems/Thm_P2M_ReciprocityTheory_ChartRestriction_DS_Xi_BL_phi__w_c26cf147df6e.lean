-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi__w_c26cf147df6e
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi__w_c26cf147df6e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:29.515186+00:00
-- url     : https://prove2.me/theorems/0f52e4e7-6da0-58e0-81f6-d7dcb6795d12
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi BL phi  w c26cf147df6e: P2 M Reciprocity Theory Chart Restriction DS Xi BL phi  w c26cf147df6e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi BL phi  w c26cf147df6e construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi BL phi  w c26cf147df6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermExpand.lean#L92-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable (k n : ℕ)

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi__w_c26cf147df6e (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV' k n a (wp k n i) = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«BL».«phi'_w» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_phi__w_c26cf147df6e
