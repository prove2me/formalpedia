-- Prove2me | Theorems.Thm_Reformulated_TransposeInverseTheory_map_transposeInv
-- name    : Reformulated.TransposeInverseTheory.map_transposeInv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:42.748078+00:00
-- url     : https://prove2.me/theorems/cf4b1c8b-beda-4a8a-bfef-5e6ffd48be26
-- title:
--   Transpose Inverse Theory: map transpose Inv
-- statement:
--   The Transpose Inverse Theory construction uses the map transpose Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean#L52-L55

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.TransposeInverseTheory
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

theorem Reformulated.TransposeInverseTheory.map_transposeInv {S : Type*} [CommRing S] (f : R →+* S) (g : GL n R) :
    GeneralLinearGroup.map f (transposeInv g) = transposeInv (GeneralLinearGroup.map f g) := by sorry
