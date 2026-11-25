-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_eq_finsum_ad49380098f7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_eq_finsum_ad49380098f7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:29.236671+00:00
-- url     : https://prove2.me/theorems/47b3c13a-c9e7-5c2b-8f64-1d55159110cd
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum eq finsum ad49380098f7: P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum eq finsum ad49380098f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum eq finsum ad49380098f7 construction uses the P2 M Ground Theory Heights  Heights Inter Swap Cycles Alt sum eq finsum ad49380098f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L183-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSwapCycles.lean#L183-L227

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_sum_eq_finsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
  ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_eq_finsum_ad49380098f7 {V Z : Ideal (MRing ι)} [V.IsPrime] [Z.IsPrime] {A : Type} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Algebra (MRing ι) A]
    (h : IsLocData (MRing ι) A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal (MRing ι), Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap (MRing ι) A) = Q)
    {f t : MRing ι} (hZr : IsRelevant Z)
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) (hfV : f ∉ V) :
    ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ algebraMap (MRing ι) A f ∈ p.asIdeal),
        ordLoc p (algebraMap (MRing ι) A f) * ordMod p (algebraMap (MRing ι) A t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SwapCyclesAlt».«sum_eq_finsum» := P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_eq_finsum_ad49380098f7
