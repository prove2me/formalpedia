-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_deriv_finsetProd_eq_zero
-- name    : ReciprocityTheory.PGsh.deriv_finsetProd_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:37:29.966376+00:00
-- url     : https://prove2.me/theorems/9dc4856b-7e78-4a6e-9677-59121cbc2727
-- title:
--   PGsh: deriv finset Prod eq zero
-- statement:
--   The PGsh construction uses the deriv finset Prod eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L29-L32

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
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem ReciprocityTheory.PGsh.deriv_finsetProd_eq_zero {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (t : Finset ι)
    (P : ι → A) (h : ∀ k ∈ t, D (P k) = 0) : D (∏ k ∈ t, P k) = 0 := by sorry
