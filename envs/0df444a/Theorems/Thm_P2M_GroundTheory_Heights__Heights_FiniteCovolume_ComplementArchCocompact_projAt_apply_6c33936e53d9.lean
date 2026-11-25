-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_apply_6c33936e53d9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_apply_6c33936e53d9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:55.469532+00:00
-- url     : https://prove2.me/theorems/cf87a8ef-5347-56f6-bfc6-bb731e6935eb
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At apply 6c33936e53d9: P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At apply 6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At apply 6c33936e53d9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At apply 6c33936e53d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L47-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsZsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementArchCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementArchCocompact
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_apply_6c33936e53d9 (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (Y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    projAt h v x₀ w₀ Y w = Y w - (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v x₀ w -
      (star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v w₀ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementArchCocompact».«projAt_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_apply_6c33936e53d9
