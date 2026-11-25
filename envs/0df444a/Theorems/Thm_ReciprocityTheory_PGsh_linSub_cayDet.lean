-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_linSub_cayDet
-- name    : ReciprocityTheory.PGsh.linSub_cayDet
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:56.786213+00:00
-- url     : https://prove2.me/theorems/5de1a958-9641-54d6-9bd4-f7f0b02a3e57
-- title:
--   PGsh: lin Sub cay Det
-- statement:
--   The PGsh construction uses the lin Sub cay Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L181-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L181-L190

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.PGsh.linSub_cayDet (g : Matrix (Fin n) (Fin n) R) :
    linSub g (cayDet n R) = C g.det * cayDet n R := by sorry
