-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_basisMatrix_apply__0938c75f59f5
-- name    : P2M_GroundTheory_Heights__Heights_basisMatrix_apply__0938c75f59f5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:41.398964+00:00
-- url     : https://prove2.me/theorems/640a2cad-5460-4475-a25d-6bfc141471bb
-- title:
--   P2 M Ground Theory Heights  Heights basis Matrix apply  0938c75f59f5: P2 M Ground Theory Heights  Heights basis Matrix apply  0938c75f59f5
-- statement:
--   The P2 M Ground Theory Heights  Heights basis Matrix apply  0938c75f59f5 construction uses the P2 M Ground Theory Heights  Heights basis Matrix apply  0938c75f59f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Covolume.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Covolume.lean#L43-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module
open scoped Kronecker
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_basisMatrix_apply__0938c75f59f5 (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«basisMatrix_apply'» := P2M_GroundTheory_Heights__Heights_basisMatrix_apply__0938c75f59f5
