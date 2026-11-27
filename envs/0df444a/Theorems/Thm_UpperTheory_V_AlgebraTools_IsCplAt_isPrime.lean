-- Prove2me | Theorems.Thm_UpperTheory_V_AlgebraTools_IsCplAt_isPrime
-- name    : UpperTheory.V.AlgebraTools.IsCplAt.isPrime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:19.898255+00:00
-- url     : https://prove2.me/theorems/74a92877-f898-56ca-8379-347431ad3fa4
-- title:
--   Is Cpl At: is Prime
-- statement:
--   The Is Cpl At construction uses the is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/AlgebraTools/IsCplAtSelf.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/AlgebraTools/IsCplAtSelf.lean#L16-L19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_IsCplAtSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.isPrime {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by sorry
