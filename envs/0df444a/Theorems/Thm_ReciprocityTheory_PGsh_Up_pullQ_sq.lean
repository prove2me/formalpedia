-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_pullQ_sq
-- name    : ReciprocityTheory.PGsh.Up.pullQ_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:44:58.95421+00:00
-- url     : https://prove2.me/theorems/0c64a74b-2401-5e60-8070-4fbaa5959da1
-- title:
--   Up: pull Q sq
-- statement:
--   The Up construction uses the pull Q sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PowMemCarrier.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PowMemCarrier.lean#L52-L62

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
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
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable (K : AddSubgroup N) [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]

theorem ReciprocityTheory.PGsh.Up.pullQ_sq (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) {z : N ⧸ K → C}
    (hz : z ∈ sqIdeal (augIdeal AQ.carrier)) :
    pullQ (R := R) K z ∈ sqIdeal (augIdeal AA.carrier) := by sorry
