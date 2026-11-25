-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_pderiv_linSub_X
-- name    : ReciprocityTheory.PGsh.pderiv_linSub_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:24.951518+00:00
-- url     : https://prove2.me/theorems/f82e2e9a-bffc-5d95-8ac0-2fd7275e71a3
-- title:
--   PGsh: pderiv lin Sub X
-- statement:
--   The PGsh construction uses the pderiv lin Sub X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L73-L79

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

theorem ReciprocityTheory.PGsh.pderiv_linSub_X (g : Matrix (Fin n) (Fin n) R) (a b : Fin n) (v : Fin n × Fin n) :
    pderiv (a, b) (linSub g (X v)) = if v.2 = b then C (g v.1 a) else 0 := by sorry
