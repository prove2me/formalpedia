-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_out__2641bc948268
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_out__2641bc948268
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:42.882364+00:00
-- url     : https://prove2.me/theorems/a5cf4743-b9c2-44e4-8e93-a3e112f3cd67
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi BL io out  2641bc948268: P2 M Reciprocity Theory Chart Restriction DS Xi BL io out  2641bc948268
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi BL io out  2641bc948268 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi BL io out  2641bc948268 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean#L118-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
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
variable {k r' : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_out__2641bc948268 (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«BL».«io_out'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_io_out__2641bc948268
