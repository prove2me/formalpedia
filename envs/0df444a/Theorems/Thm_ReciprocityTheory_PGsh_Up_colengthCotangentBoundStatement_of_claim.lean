-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_colengthCotangentBoundStatement_of_claim
-- name    : ReciprocityTheory.PGsh.Up.colengthCotangentBoundStatement_of_claim
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:08:27.25288+00:00
-- url     : https://prove2.me/theorems/c9d0aa9e-0175-46c5-add5-fa600ed132d0
-- title:
--   Up: colength Cotangent Bound Statement of claim
-- statement:
--   The Up construction uses the colength Cotangent Bound Statement of claim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthCotangentBoundStatementOfClaim.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ColengthCotangentBoundStatementOfClaim.lean#L68-L72

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.colengthCotangentBoundStatement_of_claim (hcl : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 → ColengthCotangentValuation p C v R) : ColengthCotangentBoundStatement := by sorry
