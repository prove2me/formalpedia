-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_trace_mul_posSemidef_nonneg
-- name    : ShadowTomography.UpperBound.trace_mul_posSemidef_nonneg
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:17.665618+00:00
-- url     : https://prove2.me/theorems/33f5359a-dcbf-4b25-8182-257f82b4514d
-- title:
--   The trace of a product of two positive semidefinite matrices is nonnegative
-- statement:
--   Let $A$ and $B$ be positive semidefinite complex matrices of the same size. Then
--   $$
--   \operatorname{Re}\operatorname{Tr}(AB)\ge0 .
--   $$
--   (In fact $\operatorname{Tr}(AB)=\operatorname{Tr}(B^{1/2}AB^{1/2})$ is a nonnegative real number.)
--
--   In quantum information this says that Born-rule probabilities $\operatorname{Tr}(P\rho)$ of POVM elements are nonnegative, and that effects have acceptance probabilities in $[0,1]$; it is used throughout the shadow-tomography argument (pp. 15-19).
-- source:
--   S. Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, https://arxiv.org/abs/1711.01053, Section 5 (proof of Theorem 2), pp. 15-19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound

/-- **K5d.** The trace of a product of two positive semidefinite matrices has nonnegative real
part. -/
theorem trace_mul_posSemidef_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  sorry

end ShadowTomography.UpperBound
