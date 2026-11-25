-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsZsmulMem_exists_zsmul_mem__0d93729e89df
-- name    : P2M_UpperTheory_Reformulated_B_ExistsZsmulMem_exists_zsmul_mem__0d93729e89df
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:24.075725+00:00
-- url     : https://prove2.me/theorems/3bf71fb3-eca5-58e0-9493-afa813775faf
-- title:
--   P2 M Upper Theory Reformulated B Exists Zsmul Mem exists zsmul mem  0d93729e89df: P2 M Upper Theory Reformulated B Exists Zsmul Mem exists zsmul mem  0d93729e89df
-- statement:
--   The P2 M Upper Theory Reformulated B Exists Zsmul Mem exists zsmul mem  0d93729e89df construction uses the P2 M Upper Theory Reformulated B Exists Zsmul Mem exists zsmul mem  0d93729e89df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsZsmulMem.lean#L4-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsZsmulMem.lean#L4-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsZsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_ExistsZsmulMem_exists_zsmul_mem__0d93729e89df.{u_1, u_2} :
    ∀ {E : Type u_1} [inst : Field E] [NumberField E] {W : Type u_2} [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice E La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by sorry

alias «UpperTheory».«Reformulated».«B».«ExistsZsmulMem».«exists_zsmul_mem».«» := P2M_UpperTheory_Reformulated_B_ExistsZsmulMem_exists_zsmul_mem__0d93729e89df
