-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d
-- name    : P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:52.577967+00:00
-- url     : https://prove2.me/theorems/b22cf878-31a2-4a36-a26d-94eb5b3e2766
-- title:
--   P2 M Upper Theory Reformulated B Ydb5 exists Unique fixed Point  f2868b5b329d: P2 M Upper Theory Reformulated B Ydb5 exists Unique fixed Point  f2868b5b329d
-- statement:
--   The P2 M Upper Theory Reformulated B Ydb5 exists Unique fixed Point  f2868b5b329d construction uses the P2 M Upper Theory Reformulated B Ydb5 exists Unique fixed Point  f2868b5b329d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsUniqueFixedPoint.lean#L16-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsUniqueFixedPoint.lean#L16-L44

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d.{u_1, u_2} :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommRing R] (Φ : MvPowerSeries σ R → MvPowerSeries σ R),
      (∀ (f g : MvPowerSeries σ R) (n : ℕ), (↑n : ℕ∞) ≤ (f - g).order → (↑(n + (1 : ℕ)) : ℕ∞) ≤ (Φ f - Φ g).order) →
        ∃! f : MvPowerSeries σ R, Φ f = f := by sorry

alias «UpperTheory».«Reformulated».«B».«Ydb5».«existsUnique_fixedPoint».«» := P2M_UpperTheory_Reformulated_B_Ydb5_existsUnique_fixedPoint__f2868b5b329d
