-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightOfCycle_gaussNorm_eq_iSup_6f64d070639a
-- name    : P2M_GroundTheory_Heights__Heights_HeightOfCycle_gaussNorm_eq_iSup_6f64d070639a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:56.497391+00:00
-- url     : https://prove2.me/theorems/2eae1fdf-753d-4e8d-8f3f-ff11bfe04bbe
-- title:
--   P2 M Ground Theory Heights  Heights Height Of Cycle gauss Norm eq i Sup 6f64d070639a: P2 M Ground Theory Heights  Heights Height Of Cycle gauss Norm eq i Sup 6f64d070639a
-- statement:
--   The P2 M Ground Theory Heights  Heights Height Of Cycle gauss Norm eq i Sup 6f64d070639a construction uses the P2 M Ground Theory Heights  Heights Height Of Cycle gauss Norm eq i Sup 6f64d070639a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfCycle.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHeightOfCycle.lean#L18-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHeightOfCycle
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
open MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.HeightOfCycle
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HeightOfCycle_gaussNorm_eq_iSup_6f64d070639a {ι : Type*} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {f : MvPolynomial ι K} (hf : f ≠ 0) (S : Finset (ι →₀ ℕ)) (hS : f.support ⊆ S) :
    gaussNorm v f = ⨆ m : S, FinitePlace.equivHeightOneSpectrum.symm v (f.coeff m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HeightOfCycle».«gaussNorm_eq_iSup» := P2M_GroundTheory_Heights__Heights_HeightOfCycle_gaussNorm_eq_iSup_6f64d070639a
