-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_vecAt_e2b25eee4c71
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_vecAt_e2b25eee4c71
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:39.748483+00:00
-- url     : https://prove2.me/theorems/a42e2ed5-1579-4cb1-8108-7054640812c4
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At vec At e2b25eee4c71: P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At vec At
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At vec At e2b25eee4c71 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proj At vec At e2b25eee4c71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L57-L64

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_vecAt_e2b25eee4c71 (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (e : W) :
    projAt h v x₀ w₀ (vecAt v e) = vecAt v (ComplementExtension.proj hp e : W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementArchCocompact».«projAt_vecAt» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_vecAt_e2b25eee4c71
