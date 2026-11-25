-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_inner_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.StepA.inner_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:31.04164+00:00
-- url     : https://prove2.me/theorems/3d62a58a-9585-4ec9-8a98-6612098489ea
-- title:
--   Step A: inner eq
-- statement:
--   The Step A construction uses the inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergFactsOfInductiveInput.lean#L99-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergFactsOfInductiveInput.lean#L99-L168

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_EIntBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.StepA.inner_eq (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hk : 1 ≤ k) (A : ℝ) (s : Fin (1 + r' + 1) → ℝ)
    (μ₁ : Measure (Mt k r')) (hμ₁ : IsHaarOn (GV k r') μ₁) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∫⁻ g, (∫⁻ x', ENNReal.ofReal (gN (oneStep k r' x c (Matrix.of g) x') ^ (-A))) *
        FsE k r' (fun l => s (sc r' l)) (Matrix.of g) ∂μ₁ =
      ENNReal.ofReal (Psi k r' s x) * Qf k r' A (fun l => s (sc r' l)) μ₁ (c * (Dx k r' x : ℂ)) := by sorry
