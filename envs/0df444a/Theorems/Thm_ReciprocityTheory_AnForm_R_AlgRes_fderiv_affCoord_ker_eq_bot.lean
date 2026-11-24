-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_fderiv_affCoord_ker_eq_bot
-- name    : ReciprocityTheory.AnForm.R.AlgRes.fderiv_affCoord_ker_eq_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:23.057706+00:00
-- url     : https://prove2.me/theorems/0164ee77-6ba4-4b3d-8411-145246a0ce1a
-- title:
--   Alg Res: fderiv aff Coord ker eq bot
-- statement:
--   The Alg Res construction uses the fderiv aff Coord ker eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Immersion.lean#L9-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/Immersion.lean#L9-L77

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.AlgRes.fderiv_affCoord_ker_eq_bot {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (i : Fin R.n)
    (x : R.M) (hx : x ∈ R.src i) (hxD : (fun q => eval (R.coord i x) (R.lift i q)) ∉ conePts D)
    (p : (k : K) → ι k) (hp : ∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0)
    (j : Fin A.n) (hj : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)))
      (A.chart j x)).ker = ⊥ := by sorry
