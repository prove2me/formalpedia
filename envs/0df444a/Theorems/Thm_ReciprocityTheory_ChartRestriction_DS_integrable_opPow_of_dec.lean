-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_integrable_opPow_of_dec
-- name    : ReciprocityTheory.ChartRestriction.DS.integrable_opPow_of_dec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:19.990269+00:00
-- url     : https://prove2.me/theorems/bf3b3d6d-a851-509c-91d1-d1efbae2e431
-- title:
--   DS: integrable op Pow of dec
-- statement:
--   The DS construction uses the integrable op Pow of dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefIntVG.lean#L16-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefIntVG.lean#L16-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefIntVG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.integrable_opPow_of_dec (Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hcont : ContinuousOn Ψ {g | inUJ ε g}) (hle : ∀ g, inUJ ε g → ‖Ψ g‖ ≤ 1)
    {h : ℝ} (hq : 1 ≤ S7.q0 ε)
    (hDec : ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))))
    {N : ℝ} (hN : 0 ≤ N)
    (hthr : 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) * (N + 2 * (n : ℝ) * S7.q0 ε) < h)
    (ν : Measure (S7.UJ ε)) [ν.IsHaarMeasure] :
    Integrable (fun g : S7.UJ ε =>
      ‖Ψ (S7.toM g)‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (S7.toM g)‖ ^ N) ν := by sorry
