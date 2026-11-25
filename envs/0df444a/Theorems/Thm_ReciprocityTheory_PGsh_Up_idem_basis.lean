-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_idem_basis
-- name    : ReciprocityTheory.PGsh.Up.idem_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:22.084464+00:00
-- url     : https://prove2.me/theorems/76f114c8-4d29-4417-b26d-9ccbc3817227
-- title:
--   Up: idem basis
-- statement:
--   The Up construction uses the idem basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WdetDegreeOfSmithRestrict.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WdetDegreeOfSmithRestrict.lean#L14-L40

import Definitions.Def_ReciprocityTheory_DualLattices_EigenQuotientSmithStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_WdetDegreeOfSmithRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2

theorem ReciprocityTheory.PGsh.Up.idem_basis {S : Type} [CommRing S] [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι S) (hP : P * P = P) : ∃ (r : ℕ) (Bw : Matrix ι (Fin r) S),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin P) ∧
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ := by sorry
