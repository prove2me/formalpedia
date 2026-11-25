-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_perm_mp
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.perm_mp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:50.733262+00:00
-- url     : https://prove2.me/theorems/27fa2427-873a-5699-8d6d-6e3ee30422bf
-- title:
--   Formula FAux: perm mp
-- statement:
--   The Formula FAux construction uses the perm mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean#L109-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IndexEmbeddingBijective
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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.perm_mp (k r' : ℕ) (hk : 1 ≤ k) : MeasurePreserving (permF k r') volume volume := by sorry
