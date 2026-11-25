-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_exists_zsmul_mem_b836dd55284f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_exists_zsmul_mem_b836dd55284f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:57.390154+00:00
-- url     : https://prove2.me/theorems/dce164f5-e1d6-45cd-a7c4-89127fb6317f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact exists zsmul mem b836dd55284f: P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact exists zsmul
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact exists zsmul mem b836dd55284f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact exists zsmul mem b836dd55284f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L21-L23

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
open GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementArchCocompact
variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_exists_zsmul_mem_b836dd55284f {La : AddSubgroup W} (hL : IsLattice E La) (x : W) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementArchCocompact».«exists_zsmul_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_exists_zsmul_mem_b836dd55284f
