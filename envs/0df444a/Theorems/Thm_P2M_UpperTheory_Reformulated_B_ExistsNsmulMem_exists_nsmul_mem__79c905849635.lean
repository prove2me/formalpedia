-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsNsmulMem_exists_nsmul_mem__79c905849635
-- name    : P2M_UpperTheory_Reformulated_B_ExistsNsmulMem_exists_nsmul_mem__79c905849635
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:52.628989+00:00
-- url     : https://prove2.me/theorems/3daacf93-8655-4502-b9c1-96bbdb12450a
-- title:
--   P2 M Upper Theory Reformulated B Exists Nsmul Mem exists nsmul mem  79c905849635: P2 M Upper Theory Reformulated B Exists Nsmul Mem exists nsmul mem  79c905849635
-- statement:
--   The P2 M Upper Theory Reformulated B Exists Nsmul Mem exists nsmul mem  79c905849635 construction uses the P2 M Upper Theory Reformulated B Exists Nsmul Mem exists nsmul mem  79c905849635 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsNsmulMem.lean#L4-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsNsmulMem.lean#L4-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_ExistsNsmulMem_exists_nsmul_mem__79c905849635.{u_1, u_2} :
    ∀ {E : Type u_1} {W : Type u_2} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice E La →
      ∀ (w : W),
        ∃ (d : ℕ),
          (0 : ℕ) < d ∧
            d • w ∈ La := by sorry

alias «UpperTheory».«Reformulated».«B».«ExistsNsmulMem».«exists_nsmul_mem».«» := P2M_UpperTheory_Reformulated_B_ExistsNsmulMem_exists_nsmul_mem__79c905849635
