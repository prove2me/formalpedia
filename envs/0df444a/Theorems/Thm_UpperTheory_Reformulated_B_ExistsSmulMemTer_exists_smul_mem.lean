-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ExistsSmulMemTer_exists_smul_mem
-- name    : UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:24.185815+00:00
-- url     : https://prove2.me/theorems/b460a76d-83b7-4427-a82d-7b997a926d61
-- title:
--   Exists Smul Mem Ter: exists smul mem
-- statement:
--   The Exists Smul Mem Ter construction uses the exists smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsSmulMemTer.lean#L3-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsSmulMemTer.lean#L3-L34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (M : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑M : Set V),
      ∃ (a : NumberField.RingOfIntegers K), a ≠ (0 : NumberField.RingOfIntegers K) ∧ a • x ∈ M := by sorry
