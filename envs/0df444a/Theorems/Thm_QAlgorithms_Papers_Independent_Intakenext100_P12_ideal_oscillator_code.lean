-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_ideal_oscillator_code
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.ideal_oscillator_code
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:43:15.649818+00:00
-- url     : https://prove2.me/theorems/7a912eb5-129e-4a4f-bd2b-5e0ab8874d3f
-- title:
--   Abstract / §IV (21)–(27): ideal single-oscillator qunit code and exact small-shift correction
-- statement:
--   Let $n\ge2$ and $\alpha>0$. Give the logical space $\mathbb C^n$ its usual inner product. Define $Jc=\sum_{j=0}^{n-1}c_j\sum_{k\in\mathbb Z}\delta_{\alpha(j+nk)}$. These sums converge against Schwartz tests, $J$ is injective, and its image is exactly the common $+1$ space of translation by $n\alpha$ and multiplication by $e^{2\pi iq/\alpha}$. Translation by $\alpha$ and multiplication by $e^{2\pi iq/(n\alpha)}$ induce the logical shift $X$ and clock $Z$, satisfying
--
--   $$ZX=e^{2\pi i/n}XZ.$$
--
--   One linear algebraic syndrome decoder, chosen before the error and logical vector, separates every displacement $e^{i(-up+vq)}$ with $|u|<\alpha/2$ and $|v|<\pi/(n\alpha)$, including finite coherent sums. There is also an isometric realization of $\mathbb C^n\otimes L^2(C)$ in physical $L^2(\mathbb R)$, where $C$ is this open error cell, given by the explicitly defined displacement integral. Thus square-integrable embedded errors preserve the logical factor. The radii obey $|uv|<\pi/(2n)$; choosing $\alpha=\sqrt{2\pi/n}$ makes the two radii equal.
--
--   This is an ideal generalized-state code, with no claim that the combs themselves are normalized physical vectors.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 1, Abstract / §IV (21)–(27): ideal single-oscillator qunit code and exact small-shift correction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Abstract/Section IV (21)–(27), PDF pp.1,4–5: the explicitly constructed nonzero ideal
qunit code, exact logical operations and a single syndrome realization for all small shifts.
No ideal comb is asserted to belong to L2. The algebraic decoder handles finite coherent
error sums; the unitary realization handles square-integrable embedded-error wavefunctions. -/
theorem ideal_oscillator_code (n : ℕ) (hn : 2 ≤ n) (alpha : ℝ) (ha : 0 < alpha) :
    Function.Injective (idealComb n alpha) ∧
    (∀ j : Fin n, ∀ f : SchwartzMap ℝ ℂ, Summable (fun k : ℤ => f (combSupportPoint n alpha j k))) ∧
    (∀ T : SchwartzMap ℝ ℂ → ℂ,
      IsIdealStabilized n alpha T ↔ ∃ c : Fin n → ℂ, idealComb n alpha c = T) ∧
    (∀ c : Fin n → ℂ,
      displacedComb n alpha alpha 0 c = idealComb n alpha (logicalCycle n c) ∧
      displacedComb n alpha 0 (2 * Real.pi / (n * alpha)) c = idealComb n alpha (logicalClock n c) ∧
      logicalClock n (logicalCycle n c) =
        fun j => cisPhase (2 * Real.pi / n) * logicalCycle n (logicalClock n c) j) ∧
    (∃ R : (SchwartzMap ℝ ℂ → ℂ) →ₗ[ℂ] ({uv // uv ∈ errorCell n alpha} → Fin n → ℂ),
      ∀ (e : {uv // uv ∈ errorCell n alpha}) (c : Fin n → ℂ),
        R (displacedComb n alpha e.val.1 e.val.2 c) = fun s => if s = e then c else 0) ∧
    HasExactRealization n alpha ∧
    (∀ u v : ℝ, |u| < alpha / 2 → |v| < Real.pi / (n * alpha) →
      |u * v| < Real.pi / (2 * n)) ∧
    Real.pi / (n * Real.sqrt (2 * Real.pi / n)) = Real.sqrt (2 * Real.pi / n) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
