-- Prove2me | Theorems.Thm_P2M_GlobalTheory_adicLevel__closedPoint_ce2e53ef22fe
-- name    : P2M_GlobalTheory_adicLevel__closedPoint_ce2e53ef22fe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:48.965794+00:00
-- url     : https://prove2.me/theorems/827b2b4e-463e-4b0a-827c-bb7d86573d2e
-- title:
--   P2 M Global Theory adic Level  closed Point ce2e53ef22fe: P2 M Global Theory adic Level  closed Point ce2e53ef22fe
-- statement:
--   The P2 M Global Theory adic Level  closed Point ce2e53ef22fe construction uses the P2 M Global Theory adic Level  closed Point ce2e53ef22fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L238-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem P2M_GlobalTheory_adicLevel__closedPoint_ce2e53ef22fe (hI : I ≠ ⊤) (n : ℕ) :
    haveI := isLocalRing_quotient_pow hI n
    adicLevelι I (n + 1) (closedPoint (R ⧸ I ^ (n + 1))) = closedPoint R := by sorry

alias «GlobalTheory».«adicLevelι_closedPoint» := P2M_GlobalTheory_adicLevel__closedPoint_ce2e53ef22fe
