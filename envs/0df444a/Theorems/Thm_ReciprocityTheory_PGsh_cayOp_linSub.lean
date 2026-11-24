-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_cayOp_linSub
-- name    : ReciprocityTheory.PGsh.cayOp_linSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:26.566919+00:00
-- url     : https://prove2.me/theorems/08a14e84-af75-443d-b494-b2058db9d0a3
-- title:
--   PGsh: cay Op lin Sub
-- statement:
--   The PGsh construction uses the cay Op lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L151-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L151-L179

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

theorem ReciprocityTheory.PGsh.cayOp_linSub (g : Matrix (Fin n) (Fin n) R) (q : MvPolynomial (Fin n × Fin n) R) :
    cayOp n R (linSub g q) = C g.det * linSub g (cayOp n R q) := by sorry
