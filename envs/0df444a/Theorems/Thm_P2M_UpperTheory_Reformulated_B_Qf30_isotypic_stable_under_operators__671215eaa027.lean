-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qf30_isotypic_stable_under_operators__671215eaa027
-- name    : P2M_UpperTheory_Reformulated_B_Qf30_isotypic_stable_under_operators__671215eaa027
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:40.784414+00:00
-- url     : https://prove2.me/theorems/c06bdd66-fd67-4f60-ae42-536f0858a19d
-- title:
--   P2 M Upper Theory Reformulated B Qf30 isotypic stable under operators  671215eaa027: P2 M Upper Theory Reformulated B Qf30 isotypic stable under operators  671215eaa027
-- statement:
--   The P2 M Upper Theory Reformulated B Qf30 isotypic stable under operators  671215eaa027 construction uses the P2 M Upper Theory Reformulated B Qf30 isotypic stable under operators  671215eaa027 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsotypicStableUnderOperators.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsotypicStableUnderOperators.lean#L58-L75

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableUnderOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qf30_isotypic_stable_under_operators__671215eaa027.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu := by sorry

alias «UpperTheory».«Reformulated».«B».«Qf30».«isotypic_stable_under_operators» := P2M_UpperTheory_Reformulated_B_Qf30_isotypic_stable_under_operators__671215eaa027
