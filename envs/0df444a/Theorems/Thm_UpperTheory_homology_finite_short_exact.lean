-- Prove2me | Theorems.Thm_UpperTheory_homology_finite_short_exact
-- name    : UpperTheory.homology_finite_short_exact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:49.196568+00:00
-- url     : https://prove2.me/theorems/7e6f665a-2172-46ce-a00c-3ac6f0c6f990
-- title:
--   Upper Theory: homology finite short exact
-- statement:
--   The Upper Theory construction uses the homology finite short exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HomologyFiniteShortExact.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HomologyFiniteShortExact.lean#L23-L32

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomologyFiniteShortExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open UpperTheory
universe v u w

theorem UpperTheory.homology_finite_short_exact {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)} (hS : S.ShortExact) (i : ι) :
    (Finite (S.X₁.homology i) → Finite (S.X₃.homology i) → Finite (S.X₂.homology i)) ∧
    (IsNoetherianRing R → Module.Finite R (S.X₁.homology i) →
      Module.Finite R (S.X₃.homology i) → Module.Finite R (S.X₂.homology i)) := by sorry
