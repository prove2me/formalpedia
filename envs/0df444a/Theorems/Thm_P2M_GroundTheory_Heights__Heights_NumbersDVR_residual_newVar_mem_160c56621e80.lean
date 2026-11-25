-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_residual_newVar_mem_160c56621e80
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_residual_newVar_mem_160c56621e80
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:53.386412+00:00
-- url     : https://prove2.me/theorems/246e0a10-b533-4529-a379-d9ad30eecb74
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR residual new Var mem 160c56621e80: P2 M Ground Theory Heights  Heights Numbers DVR residual new Var mem 160c56621e80
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR residual new Var mem 160c56621e80 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR residual new Var mem 160c56621e80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ResidualNewVarMem.lean#L14-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ResidualNewVarMem.lean#L14-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RingKrullDimQuotientLeComapAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ResidualNewVarMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_residual_newVar_mem_160c56621e80 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u}
    [CommRing R] [IsNoetherianRing R] {P : Ideal (MRing ι R)} [P.IsPrime] {s g f m : MRing ι R}
    (e : K → ℕ) (hfP : f ∉ P) (hmP : m ∉ P) {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)}
    (hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G')
    (hres : 0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G') :
    ∀ j, j ≠ none → (newVar j : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«residual_newVar_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_residual_newVar_mem_160c56621e80
