-- Prove2me | Theorems.Thm_UpperTheory_multilinear_vanish_lattice
-- name    : UpperTheory.multilinear_vanish_lattice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:31:13.730421+00:00
-- url     : https://prove2.me/theorems/43bdbb84-0471-468a-9565-01c0d3337b90
-- title:
--   Upper Theory: multilinear vanish lattice
-- statement:
--   The Upper Theory construction uses the multilinear vanish lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MultilinearVanishLattice.lean#L3-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MultilinearVanishLattice.lean#L3-L39

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultilinearVanishLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.multilinear_vanish_lattice :
    ∀ {ι : Type} [Finite ι] [DecidableEq ι] {M : ι → Type} {N : Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
        [AddCommGroup N] [Module ℂ N] (T : MultilinearMap ℂ M N) (L G : ∀ i, Set (M i)),
        (∀ v : ∀ i, M i, (∀ i, v i ∈ L i) → T v = 0) →
        (∀ i, ∀ w ∈ G i, ∃ w0 ∈ L i, ∀ v : ∀ i, M i, T (Function.update v i w0) = 0 → T (Function.update v i w) = 0) →
        ∀ v : ∀ i, M i, (∀ i, v i ∈ Submodule.span ℂ (G i)) → T v = 0 := by sorry
