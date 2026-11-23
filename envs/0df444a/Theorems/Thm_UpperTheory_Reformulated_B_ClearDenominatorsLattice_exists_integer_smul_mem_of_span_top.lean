-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ClearDenominatorsLattice_exists_integer_smul_mem_of_span_top
-- name    : UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:56.556842+00:00
-- url     : https://prove2.me/theorems/de8884e2-7ebd-4e8d-835c-8464ed98cd77
-- title:
--   Clear Denominators Lattice: exists integer smul mem of span top
-- statement:
--   The Clear Denominators Lattice construction uses the exists integer smul mem of span top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ClearDenominatorsLattice.lean#L3-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ClearDenominatorsLattice.lean#L3-L33

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClearDenominatorsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ →
      ∀ (x : V), ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by sorry
