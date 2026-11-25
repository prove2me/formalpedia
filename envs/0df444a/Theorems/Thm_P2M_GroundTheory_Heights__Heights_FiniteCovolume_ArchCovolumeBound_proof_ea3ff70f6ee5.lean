-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchCovolumeBound_proof_ea3ff70f6ee5
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchCovolumeBound_proof_ea3ff70f6ee5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:38.641844+00:00
-- url     : https://prove2.me/theorems/71c5fe8d-e3ad-5fbd-b660-912def80f9ca
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Arch Covolume Bound proof ea3ff70f6ee5: P2 M Ground Theory Heights  Heights Finite Covolume Arch Covolume Bound proof ea3ff70f6ee5
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Arch Covolume Bound proof ea3ff70f6ee5 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Arch Covolume Bound proof ea3ff70f6ee5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchCovolumeBound.lean#L21-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchCovolumeBound.lean#L21-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordEmbedBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StIntegralFormCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StDualLatticeMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordLatticeFullRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchCovolumeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchCovolumeBound_proof_ea3ff70f6ee5 (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : CoordEmbedBasis.Statement E ι)
    (h₂ : IntegralFormCovolume.Statement (ι → E) (InfinitePlace E → ι → ℂ)
      (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E)))
    (h₃ : TraceHermNondegenerate.Statement h v) (h₄ : DualLatticeMultiple.Statement h)
    (h₅ : CoordLatticeFullRank.Statement v) : ArchCovolumeBound.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ArchCovolumeBound».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchCovolumeBound_proof_ea3ff70f6ee5
