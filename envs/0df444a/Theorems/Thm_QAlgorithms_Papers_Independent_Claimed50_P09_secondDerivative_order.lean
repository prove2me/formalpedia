-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P09_secondDerivative_order
-- name    : QAlgorithms.Papers.Independent.Claimed50.P09.secondDerivative_order
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:20:16.430995+00:00
-- url     : https://prove2.me/theorems/99d773fb-a394-4b5e-b78e-0bb31a20fd55
-- title:
--   Order comparison of second derivatives at a common zero minimum
-- statement:
--   Let $f,h:\mathbb R\to\mathbb R$ be twice differentiable functions on the whole real line. Suppose
--
--   $$
--   f(0)=h(0)=f'(0)=h'(0)=0,
--   \qquad f(x)\le h(x)\quad\text{for every }x\in\mathbb R.
--   $$
--
--   Then
--
--   $$
--   f''(0)\le h''(0).
--   $$
--
--   This scalar comparison transfers a pointwise divergence inequality to a comparison of Fisher information.
--
--   **Formalization Note** Twice differentiable means that each function and its first derivative are differentiable everywhere. No continuity of the second derivatives is required.
-- source:
--   Contractivity properties of a quantum diffusion semigroup, arXiv:1607.04242v6, PDF p. 29, Lemma 3 (Appendix C)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P09

namespace QAlgorithms.Papers.Independent.Claimed50.P09

/-- Lemma 3, Appendix C, PDF p.29: globally twice differentiable real
functions ordered pointwise, with both values and both slopes zero at the
origin, have second derivatives ordered at the origin. Differentiability of
the first derivatives is required explicitly, so `deriv` never supplies a
default value. No continuity of the second derivatives is assumed. -/
theorem secondDerivative_order (f h : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (hf2 : Differentiable ℝ (deriv f)) (hh2 : Differentiable ℝ (deriv h))
    (hf0 : f 0 = 0) (hh0 : h 0 = 0)
    (hfSlope : deriv f 0 = 0) (hhSlope : deriv h 0 = 0)
    (horder : ∀ x : ℝ, f x ≤ h x) :
    deriv (deriv f) 0 ≤ deriv (deriv h) 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P09
