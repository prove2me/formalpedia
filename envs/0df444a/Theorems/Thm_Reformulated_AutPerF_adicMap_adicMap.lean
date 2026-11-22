-- Prove2me | Theorems.Thm_Reformulated_AutPerF_adicMap_adicMap
-- name    : Reformulated.AutPerF.adicMap_adicMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:09.924939+00:00
-- url     : https://prove2.me/theorems/a050bdf9-93b6-4924-b80a-9165a8eca5db
-- title:
--   Aut Per F: adic Map adic Map
-- statement:
--   The Aut Per F construction uses the adic Map adic Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L64-L72

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

theorem Reformulated.AutPerF.adicMap_adicMap (I : Ideal A) (J : Ideal B) (K : Ideal C) (f : A →+* B) (g : B →+* C)
    (e : A →+* C) (h : I ≤ J.comap f) (h' : J ≤ K.comap g) (h'' : I ≤ K.comap e)
    (he : ∀ a, g (f a) = e a) (x : AdicCompletion I A) :
    adicMap J K g h' (adicMap I J f h x) = adicMap I K e h'' x := by sorry
