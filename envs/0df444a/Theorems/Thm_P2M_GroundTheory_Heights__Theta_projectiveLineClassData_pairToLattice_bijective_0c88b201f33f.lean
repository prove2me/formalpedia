-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_pairToLattice_bijective_0c88b201f33f
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_pairToLattice_bijective_0c88b201f33f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:48.485387+00:00
-- url     : https://prove2.me/theorems/361931ef-b26e-4c21-bfa7-8ec93c6bded8
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data pair To Lattice bijective 0c88b201f33f: P2 M Ground Theory Heights  Theta projective Line Class Data pair To Lattice bijective 0c88b201f33f
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data pair To Lattice bijective 0c88b201f33f construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data pair To Lattice bijective 0c88b201f33f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L286-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L286-L301

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_pairToLattice_bijective_0c88b201f33f (τ : ℍ) : Function.Bijective (pairToLattice τ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«pairToLattice_bijective» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_pairToLattice_bijective_0c88b201f33f
