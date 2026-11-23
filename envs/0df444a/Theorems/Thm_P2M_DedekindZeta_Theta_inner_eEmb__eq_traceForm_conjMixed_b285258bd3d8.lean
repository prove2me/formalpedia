-- Prove2me | Theorems.Thm_P2M_DedekindZeta_Theta_inner_eEmb__eq_traceForm_conjMixed_b285258bd3d8
-- name    : P2M_DedekindZeta_Theta_inner_eEmb__eq_traceForm_conjMixed_b285258bd3d8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:11:39.47478+00:00
-- url     : https://prove2.me/theorems/6f531678-0971-4123-ac25-5d434b44ecc5
-- title:
--   P2 M Dedekind Zeta Theta inner e Emb  eq trace Form conj Mixed b285258bd3d8: P2 M Dedekind Zeta Theta inner e Emb  eq trace Form conj Mixed b285258bd3d8
-- statement:
--   **Conjugate-trace pairing identity** (caution: it is the
--   *conjugate* trace `T(cξ, ·)`, NOT `Tr(ξ··)`). The Minkowski inner product of the
--   `ℝ`-linear extension `eEmbℝ ξ` against `eEmb a` equals the trace form evaluated
--   at the conjugate `c ξ`: `B(ξ, a) = T(c ξ, a)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L397-L400
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L397-L400

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem P2M_DedekindZeta_Theta_inner_eEmb__eq_traceForm_conjMixed_b285258bd3d8 (ξ : mixedSpace K) (a : K) :
    (inner ℝ (eEmbℝ K ξ) (eEmb K a) : ℝ) = traceForm K (conjMixed K ξ) a := by sorry

alias «DedekindZeta».«Theta».«inner_eEmbℝ_eq_traceForm_conjMixed» := P2M_DedekindZeta_Theta_inner_eEmb__eq_traceForm_conjMixed_b285258bd3d8
