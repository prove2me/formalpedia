-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_LinearTermOfSubstitution_main
-- name    : UpperTheory.Reformulated.B.LinearTermOfSubstitution.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:18.843003+00:00
-- url     : https://prove2.me/theorems/e9477e26-391b-48ae-8785-0a134ab75ee8
-- title:
--   Linear Term Of Substitution: main
-- statement:
--   The Linear Term Of Substitution construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DegreeOneStatement.lean#L28-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DegreeOneStatement.lean#L28-L71

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegreeOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MvPowerSeries Finsupp

theorem UpperTheory.Reformulated.B.LinearTermOfSubstitution.main :
    ∀ {S : Type}
    [inst : CommRing S] {σ τ : Type} [inst_1 : Fintype σ] [DecidableEq σ] [DecidableEq τ] (a : σ → MvPowerSeries τ S),
    (∀ (s : σ), (MvPowerSeries.constantCoeff : MvPowerSeries τ S → S) (a s) = (0 : S)) →
      ∀ (f : MvPowerSeries σ S) (t : τ),
        (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (MvPowerSeries.subst a f) =
          ∑ s : σ,
            (MvPowerSeries.coeff fun₀ | s => (1 : ℕ) : MvPowerSeries σ S → S) f *
              (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (a s) := by sorry
