-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_gram_mat__78f14edbfb72
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_gram_mat__78f14edbfb72
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:11.112932+00:00
-- url     : https://prove2.me/theorems/be7a59d2-7f91-4ee7-b827-c8bfd0ce1fe5
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi BL gram mat  78f14edbfb72: P2 M Reciprocity Theory Chart Restriction DS Xi BL gram mat  78f14edbfb72
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi BL gram mat  78f14edbfb72 construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi BL gram mat  78f14edbfb72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean#L194-L196

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_gram_mat__78f14edbfb72 {N L : ℕ} (X : Fin L → Fin N → ℂ) (Xm : Matrix (Fin N) (Fin L) ℂ) (hX : ∀ p a, Xm p a = X a p) :
    (Matrix.of fun a b => star (X a) ⬝ᵥ X b) = Xmᴴ * Xm := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«BL».«gram_mat'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_gram_mat__78f14edbfb72
