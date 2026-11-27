-- Prove2me | Theorems.Thm_UpperTheory_cochain_injective_exact
-- name    : UpperTheory.cochain_injective_exact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:35.357045+00:00
-- url     : https://prove2.me/theorems/8f6c88d4-bf31-5e68-8561-359a4727577c
-- title:
--   Upper Theory: cochain injective exact
-- statement:
--   The Upper Theory construction uses the cochain injective exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CochainInjectiveExact.lean#L32-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CochainInjectiveExact.lean#L32-L86

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CochainInjectiveExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.cochain_injective_exact :
    ∀ {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] (A B C : Rep.{0, 0, 0} k G)
        (f : A ⟶ B) (g : B ⟶ C) (KA KB KC : CochainComplex (ModuleCat.{0} k) ℕ)
        (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
        (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
        (ιC : KC ⟶ groupCohomology.inhomogeneousCochains C),
        Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
        (∀ m : ℕ, Function.Injective (ιA.f m).hom) → (∀ m : ℕ, Function.Injective (ιB.f m).hom) →
        (∀ m : ℕ, Function.Injective (ιC.f m).hom) →
        (∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → C.V), (∃ y, (ιC.f m).hom y = x) ↔ IsLocallyConstant x) →
        ∃ (φ : KA ⟶ KB) (ψ : KB ⟶ KC) (w : CategoryTheory.CategoryStruct.comp φ ψ = 0),
          (CategoryTheory.ShortComplex.mk φ ψ w).ShortExact := by sorry
