-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_update_eq_68b7d079fabf
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_update_eq_68b7d079fabf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:34.900115+00:00
-- url     : https://prove2.me/theorems/aea80b80-bba2-41f3-9068-caaea627e226
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance update eq 68b7d079fabf: P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance update eq 68b7d079fabf
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance update eq 68b7d079fabf construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance update eq 68b7d079fabf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIsomInvariance.lean#L72-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIsomInvariance.lean#L72-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIsomInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_update_eq_68b7d079fabf (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) (j : Fin n)
    (B : HermLine ι) (hP : IsArithVar P n) (hL : ∀ i, IsSmoothHerm (L i)) (hB : IsSmoothHerm B)
    (hLB : IsIsometricOn P (L j) B) : I P n L = I P n (Function.update L j B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IsomInvariance».«update_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_update_eq_68b7d079fabf
