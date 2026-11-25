-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_WeightedDegree_cycEval_divCycle_map_7da0b59b078d
-- name    : P2M_GroundTheory_Heights__Heights_WeightedDegree_cycEval_divCycle_map_7da0b59b078d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:51.558198+00:00
-- url     : https://prove2.me/theorems/af9c44f2-433a-467f-9475-1392eb57b8a9
-- title:
--   P2 M Ground Theory Heights  Heights Weighted Degree cyc Eval div Cycle map 7da0b59b078d: P2 M Ground Theory Heights  Heights Weighted Degree cyc Eval div Cycle map 7da0b59b078d
-- statement:
--   The P2 M Ground Theory Heights  Heights Weighted Degree cyc Eval div Cycle map 7da0b59b078d construction uses the P2 M Ground Theory Heights  Heights Weighted Degree cyc Eval div Cycle map 7da0b59b078d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L74-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/WeightedHomogeneousComponentMap.lean#L74-L163

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
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
open MvPolynomial NumbersDVR
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.WeightedDegree
variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']
include M₀

theorem P2M_GroundTheory_Heights__Heights_WeightedDegree_cycEval_divCycle_map_7da0b59b078d (P : Ideal (MRing ι R)) (f : MRing ι R)
    (hdisj : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
      Disjoint ((M₀.map (C (σ := Σ k, ι k)) : Submonoid (MRing ι R)) : Set (MRing ι R)) W)
    (n : Ideal (MRing ι R') → ℤ) :
    cycEval (fun W ↦ n (W.map (algebraMap (MRing ι R) (MRing ι R')))) (divCycle P f) =
      cycEval n (divCycle (P.map (algebraMap (MRing ι R) (MRing ι R')))
        (algebraMap (MRing ι R) (MRing ι R') f)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«WeightedDegree».«cycEval_divCycle_map» := P2M_GroundTheory_Heights__Heights_WeightedDegree_cycEval_divCycle_map_7da0b59b078d
