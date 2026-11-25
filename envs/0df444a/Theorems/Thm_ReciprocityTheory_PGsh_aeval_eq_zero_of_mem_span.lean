-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_aeval_eq_zero_of_mem_span
-- name    : ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:18.024415+00:00
-- url     : https://prove2.me/theorems/0ae1ea82-276e-47be-8603-f1b3b3503ad1
-- title:
--   PGsh: aeval eq zero of mem span
-- statement:
--   The PGsh construction uses the aeval eq zero of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L203-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L203-L212

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}

theorem ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span (x : Fin d → A) (hxp : ∀ j, x j ^ p = 0)
    {P : MvPolynomial (Fin d) R}
    (hP : P ∈ Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p)) :
    aeval x P = 0 := by sorry
