-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_index_embedding_bijective
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.index_embedding_bijective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:48:04.254241+00:00
-- url     : https://prove2.me/theorems/0f369818-7b49-4a2b-a48e-a1ecad45d8f1
-- title:
--   Formula FAux: index embedding bijective
-- statement:
--   The Formula FAux construction uses the index embedding bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean#L97-L103

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.index_embedding_bijective (k r' : ℕ) (hk : 1 ≤ k) : Function.Bijective (ix2 k r') := by sorry
