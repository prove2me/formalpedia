-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_IK_mul_le
-- name    : ReciprocityTheory.PGsh.Up.IK_mul_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:47:41.365583+00:00
-- url     : https://prove2.me/theorems/53be9296-43c1-446d-ba0e-cd61b8c26800
-- title:
--   Up: IK mul le
-- statement:
--   The Up construction uses the IK mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PowMemCarrier.lean#L64-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PowMemCarrier.lean#L64-L88

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

theorem ReciprocityTheory.PGsh.Up.IK_mul_le (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) :
    (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by sorry
