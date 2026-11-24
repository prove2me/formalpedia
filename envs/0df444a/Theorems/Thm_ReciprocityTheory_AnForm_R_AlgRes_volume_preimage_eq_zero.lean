-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_volume_preimage_eq_zero
-- name    : ReciprocityTheory.AnForm.R.AlgRes.volume_preimage_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:29.789801+00:00
-- url     : https://prove2.me/theorems/067cfe54-63cd-49b1-b2b9-eef2da57b5b2
-- title:
--   Alg Res: volume preimage eq zero
-- statement:
--   The Alg Res construction uses the volume preimage eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L229-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L229-L286

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.AlgRes.volume_preimage_eq_zero {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (j : Fin A.n) :
    MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) = 0 := by sorry
