-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_pderiv_linSub
-- name    : ReciprocityTheory.PGsh.pderiv_linSub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:37.722473+00:00
-- url     : https://prove2.me/theorems/b7c5de50-3c3a-41fe-8e6f-dcc751844192
-- title:
--   PGsh: pderiv lin Sub
-- statement:
--   The PGsh construction uses the pderiv lin Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L81-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L81-L105

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

theorem ReciprocityTheory.PGsh.pderiv_linSub (g : Matrix (Fin n) (Fin n) R) (a b : Fin n)
    (q : MvPolynomial (Fin n × Fin n) R) :
    pderiv (a, b) (linSub g q) = ∑ i, C (g i a) * linSub g (pderiv (i, b) q) := by sorry
