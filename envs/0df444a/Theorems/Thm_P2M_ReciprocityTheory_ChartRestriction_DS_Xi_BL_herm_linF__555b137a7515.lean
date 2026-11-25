-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_linF__555b137a7515
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_linF__555b137a7515
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:52.424039+00:00
-- url     : https://prove2.me/theorems/715789c3-534b-5c80-b212-ea523ad2b375
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi BL herm lin F  555b137a7515: P2 M Reciprocity Theory Chart Restriction DS Xi BL herm lin F  555b137a7515
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi BL herm lin F  555b137a7515 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi BL herm lin F  555b137a7515 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InnerBound.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InnerBound.lean#L91-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerBound
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_linF__555b137a7515 {k n : ℕ} (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (etaF k n w) (eta'F k n w) (zetaF k n w) (hcoord k n (y, s)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«BL».«herm_linF'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_herm_linF__555b137a7515
