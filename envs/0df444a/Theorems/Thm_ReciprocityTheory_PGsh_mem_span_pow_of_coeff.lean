-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_mem_span_pow_of_coeff
-- name    : ReciprocityTheory.PGsh.mem_span_pow_of_coeff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:24.24913+00:00
-- url     : https://prove2.me/theorems/1ea1bb5b-7a1c-4e3d-b2f4-c902248dd391
-- title:
--   PGsh: mem span pow of coeff
-- statement:
--   The PGsh construction uses the mem span pow of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L181-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L181-L201

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

theorem ReciprocityTheory.PGsh.mem_span_pow_of_coeff {P : MvPolynomial (Fin d) R}
    (h : ∀ β : Fin d →₀ ℕ, (∀ j, β j < p) → coeff β P = 0) :
    P ∈ Ideal.span (Set.range fun j : Fin d => (X j : MvPolynomial (Fin d) R) ^ p) := by sorry
