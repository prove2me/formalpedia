-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_WittVectorTrivializingMatrix_exists_alg
-- name    : UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:15.650539+00:00
-- url     : https://prove2.me/theorems/e44055a1-74ae-4015-ba13-653b0f8754a3
-- title:
--   Witt Vector Trivializing Matrix: exists alg
-- statement:
--   The Witt Vector Trivializing Matrix construction uses the exists alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormSubgroupOpen.lean#L500-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/NormSubgroupOpen.lean#L500-L518

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormSubgroupOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  ∀ (g : G) (f : R →+* R),
                    (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → (f : R → R) y = ((ρ : G → R ≃+* R) g : R → R) y) →
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map f) : WittVector p R → WittVector p R) =
                        W := by sorry
