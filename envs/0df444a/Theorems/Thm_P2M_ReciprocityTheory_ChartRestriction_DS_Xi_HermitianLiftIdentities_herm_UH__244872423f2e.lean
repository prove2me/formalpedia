-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_UH__244872423f2e
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_UH__244872423f2e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:29:52.624486+00:00
-- url     : https://prove2.me/theorems/03bbb32c-348d-4572-a14c-3504b81c40e9
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities herm UH  244872423f2e: P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities herm UH  244872423f2e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities herm UH  244872423f2e construction uses the P2 M Reciprocity Theory Chart Restriction DS Xi Hermitian Lift Identities herm UH  244872423f2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkMulVecMulVec.lean#L15-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_UH__244872423f2e [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Xi».«HermitianLiftIdentities».«herm_UH'» := P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_herm_UH__244872423f2e
