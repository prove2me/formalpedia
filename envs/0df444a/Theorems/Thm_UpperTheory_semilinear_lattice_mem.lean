-- Prove2me | Theorems.Thm_UpperTheory_semilinear_lattice_mem
-- name    : UpperTheory.semilinear_lattice_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:56.408915+00:00
-- url     : https://prove2.me/theorems/b62cf238-a8f3-4736-9afb-9af92f278189
-- title:
--   Upper Theory: semilinear lattice mem
-- statement:
--   The Upper Theory construction uses the semilinear lattice mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SemilinearLatticeMem.lean#L3-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SemilinearLatticeMem.lean#L3-L38

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SemilinearLatticeMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.semilinear_lattice_mem :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by sorry
