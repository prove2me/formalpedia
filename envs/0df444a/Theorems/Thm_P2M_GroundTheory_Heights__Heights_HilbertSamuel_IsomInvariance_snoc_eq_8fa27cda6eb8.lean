-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_snoc_eq_8fa27cda6eb8
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_snoc_eq_8fa27cda6eb8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:55.665592+00:00
-- url     : https://prove2.me/theorems/2b04c026-4c36-50de-b509-6cc5cf74723b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance snoc eq 8fa27cda6eb8: P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance snoc eq 8fa27cda6eb8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance snoc eq 8fa27cda6eb8 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance snoc eq 8fa27cda6eb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIsomInvariance.lean#L27-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIsomInvariance.lean#L27-L70

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_snoc_eq_8fa27cda6eb8 (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → HermLine ι) (A B : HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IsomInvariance».«snoc_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_snoc_eq_8fa27cda6eb8
