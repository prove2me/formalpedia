-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_vecAt_smul_apply_86caeadfe780
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_vecAt_smul_apply_86caeadfe780
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:00.656187+00:00
-- url     : https://prove2.me/theorems/53726acc-b306-5e63-bd55-3279a94151e9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact vec At smul apply 86caeadfe780: P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact vec At smul
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact vec At smul apply 86caeadfe780 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact vec At smul apply 86caeadfe780 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L53-L55

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
omit [NumberField E] [IsTotallyComplex E] [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_vecAt_smul_apply_86caeadfe780 (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementArchCocompact».«vecAt_smul_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_vecAt_smul_apply_86caeadfe780
