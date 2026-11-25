-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_AdmissibleSchurLemma_schur_adm
-- name    : UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:16.1087+00:00
-- url     : https://prove2.me/theorems/9d7ca1ad-c5c5-4e7e-9c37-83d1b9fff8db
-- title:
--   Admissible Schur Lemma: schur adm
-- statement:
--   The Admissible Schur Lemma construction uses the schur adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AdmissibleSchurLemma.lean#L73-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/AdmissibleSchurLemma.lean#L73-L137

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AdmissibleSchurLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.AdmissibleSchurLemma.schur_adm :
    ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          ∀ (N : Type) [inst_3 : AddCommGroup N] [inst_4 : _root_.Module ℂ N] (π : Representation ℂ G N),
            π.IsIrreducible →
              UpperTheory.Reformulated.B.AdmissibleSchurLemma.IsAdmissible π →
                ∀ (φ : N →ₗ[ℂ] N),
                  (∀ (g : G) (x : N),
                      (φ : N → N) (((π : G → N →ₗ[ℂ] N) g : N → N) x) = ((π : G → N →ₗ[ℂ] N) g : N → N) ((φ : N → N) x)) →
                    ∃ (c : ℂ), φ = c • LinearMap.id := by sorry
