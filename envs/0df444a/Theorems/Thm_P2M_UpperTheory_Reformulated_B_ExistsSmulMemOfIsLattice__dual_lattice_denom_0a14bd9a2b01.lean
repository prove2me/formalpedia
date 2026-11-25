-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsSmulMemOfIsLattice__dual_lattice_denom_0a14bd9a2b01
-- name    : P2M_UpperTheory_Reformulated_B_ExistsSmulMemOfIsLattice__dual_lattice_denom_0a14bd9a2b01
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:19.472637+00:00
-- url     : https://prove2.me/theorems/46d28043-32c6-4dad-9827-19505d98f585
-- title:
--   P2 M Upper Theory Reformulated B Exists Smul Mem Of Is Lattice  dual lattice denom 0a14bd9a2b01: P2 M Upper Theory Reformulated B Exists Smul Mem Of Is Lattice  dual lattice denom 0a14bd9a2b01
-- statement:
--   The P2 M Upper Theory Reformulated B Exists Smul Mem Of Is Lattice  dual lattice denom 0a14bd9a2b01 construction uses the P2 M Upper Theory Reformulated B Exists Smul Mem Of Is Lattice  dual lattice denom 0a14bd9a2b01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DualLatticeDenominator.lean#L3-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DualLatticeDenominator.lean#L3-L31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualLatticeDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_ExistsSmulMemOfIsLattice__dual_lattice_denom_0a14bd9a2b01 :
    ∀ {A : Type} [inst : CommRing A]
    [IsDomain A] {F V : Type} [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module F V] [inst_7 : _root_.Module A V] [inst_8 : IsScalarTower A F V] (Y : Submodule A V),
    Submodule.IsLattice F Y → ∀ (z : V), ∃ (a : A), a ≠ (0 : A) ∧ a • z ∈ Y := by sorry

alias «UpperTheory».«Reformulated».«B».«ExistsSmulMemOfIsLattice₂».«dual_lattice_denom» := P2M_UpperTheory_Reformulated_B_ExistsSmulMemOfIsLattice__dual_lattice_denom_0a14bd9a2b01
