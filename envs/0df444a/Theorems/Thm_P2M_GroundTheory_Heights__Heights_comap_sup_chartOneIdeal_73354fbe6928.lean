-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_sup_chartOneIdeal_73354fbe6928
-- name    : P2M_GroundTheory_Heights__Heights_comap_sup_chartOneIdeal_73354fbe6928
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:14.345579+00:00
-- url     : https://prove2.me/theorems/24fe7d72-edac-4b62-b176-1e707858d620
-- title:
--   P2 M Ground Theory Heights  Heights comap sup chart One Ideal 73354fbe6928: P2 M Ground Theory Heights  Heights comap sup chart One Ideal 73354fbe6928
-- statement:
--   The P2 M Ground Theory Heights  Heights comap sup chart One Ideal 73354fbe6928 construction uses the P2 M Ground Theory Heights  Heights comap sup chart One Ideal 73354fbe6928 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L87-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L87-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartDehom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
variable {V}

theorem P2M_GroundTheory_Heights__Heights_comap_sup_chartOneIdeal_73354fbe6928
    (hVh : ∀ f ∈ V, ∀ b : ι → ℕ, weightedHomogeneousComponent (coordDeg n) b f ∈ V)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) :
    (V ⊔ chartOneIdeal c).comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) =
      V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«comap_sup_chartOneIdeal» := P2M_GroundTheory_Heights__Heights_comap_sup_chartOneIdeal_73354fbe6928
