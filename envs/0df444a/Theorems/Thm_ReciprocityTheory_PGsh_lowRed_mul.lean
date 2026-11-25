-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_lowRed_mul
-- name    : ReciprocityTheory.PGsh.lowRed_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:57.86057+00:00
-- url     : https://prove2.me/theorems/bb152fa8-acc8-55e5-8d25-c71a53621ed1
-- title:
--   PGsh: low Red mul
-- statement:
--   The PGsh construction uses the low Red mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L120-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L120-L133

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

theorem ReciprocityTheory.PGsh.lowRed_mul {m : ℕ} {F G : MvPolynomial (Fin d) R} (hF : LowRed p m F)
    (hG : constantCoeff G = 0) (β : Fin d →₀ ℕ) (hβ : ∀ j, β j < p) (hdeg : β.degree ≤ m) :
    coeff β (F * G) = 0 := by sorry
