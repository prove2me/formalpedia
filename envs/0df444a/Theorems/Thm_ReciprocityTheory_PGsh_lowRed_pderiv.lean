-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_lowRed_pderiv
-- name    : ReciprocityTheory.PGsh.lowRed_pderiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:08.237368+00:00
-- url     : https://prove2.me/theorems/0bd7df4b-32c1-4cd4-b135-792802f75fd8
-- title:
--   PGsh: low Red pderiv
-- statement:
--   The PGsh construction uses the low Red pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L135-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L135-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R : Type*} [CommRing R] {d p : ℕ}

theorem ReciprocityTheory.PGsh.lowRed_pderiv {m : ℕ} (hp0 : (p : R) = 0) {P : MvPolynomial (Fin d) R}
    (hP : LowRed p (m + 1) P) (j : Fin d) : LowRed p m (pderiv j P) := by sorry
