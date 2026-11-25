-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_inner_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.inner_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:48:03.765173+00:00
-- url     : https://prove2.me/theorems/7c8ad48c-a2c5-4981-9337-2ee047a53800
-- title:
--   BL: inner bound
-- statement:
--   The BL construction uses the inner bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InnerBound.lean#L98-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InnerBound.lean#L98-L185

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
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.inner_bound (hIW : IW) (hF : FormulaF) (hHC : HeisConjLev) (hHA : HeisAct) (hk : 1 ≤ k)
    (s : Fin (1 + r' + 1) → ℝ) (δ γ C : ℝ) (z1 : Fin (2 * r' + k + 1) → ℂ)
    (hC : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)))
    (hcz : herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) ≠ 0)
    (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∫⁻ X : HPar k r', ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m) *
          ENNReal.ofReal ((1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by sorry
