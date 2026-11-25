-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qh9_isCM_of_conj
-- name    : UpperTheory.Reformulated.B.Qh9.isCM_of_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:57.308579+00:00
-- url     : https://prove2.me/theorems/75268e2c-6bd5-421e-a35f-35c2d166b8de
-- title:
--   Qh9: is CM of conj
-- statement:
--   The Qh9 construction uses the is CM of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsCMOfConjAlt.lean#L5-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsCMOfConjAlt.lean#L5-L55

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsCMOfConjAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField

theorem UpperTheory.Reformulated.B.Qh9.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by sorry
