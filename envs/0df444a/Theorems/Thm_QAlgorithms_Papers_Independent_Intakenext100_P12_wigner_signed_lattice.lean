-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_wigner_signed_lattice
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.wigner_signed_lattice
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:46:23.891469+00:00
-- url     : https://prove2.me/theorems/b596bee1-a72a-4bbf-bc7e-61375efec7c0
-- title:
--   §IV (28): signed Wigner comb
-- statement:
--   Let $n\ge1$, $\alpha>0$, and $0\le j<n$. Define the Wigner distribution through the explicitly paired two-point density kernel of the position comb, using $(2\pi)^{-1}\int e^{ipx}\overline{\psi(q+x/2)}\psi(q-x/2)\,dx$. With unit delta weights in the position comb,
--
--   $$W_j=\frac1{2n\alpha}\sum_{s,t\in\mathbb Z}(-1)^{st}\delta_{(\alpha j+n\alpha t/2,\,\pi s/(n\alpha))}.$$
--
--   Exactly the odd/odd parity class is negative, so three of the four parity classes are positive. The normalized symmetric lattice means that implement the source's marginal cancellation converge to the position comb at $\alpha(j+n\mathbb Z)$ and the momentum comb at $2\pi\mathbb Z/(n\alpha)$. These are generalized marginals with the stated averaging convention, not probability measures on an infinite lattice.
--
--   This formulation avoids an undefined pointwise product of distributions.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 5, §IV (28): signed Wigner comb

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section IV (28), PDF p.5: the Wigner distribution is a signed delta lattice.
The factor below fixes the arbitrary comb normalization by assigning each q delta weight one. -/
theorem wigner_signed_lattice (n : ℕ) (hn : 0 < n) (alpha : ℝ) (ha : 0 < alpha)
    (j : Fin n) :
    (∀ f : SchwartzMap (ℝ × ℝ) ℂ,
      Summable (fun ab : ℤ × ℤ => ∫ p : ℝ,
        cisPhase (p * (combSupportPoint n alpha j ab.1 - combSupportPoint n alpha j ab.2)) *
          f ((combSupportPoint n alpha j ab.1 + combSupportPoint n alpha j ab.2) / 2, p)) ∧
      wignerKernel n alpha j f =
        (2 * (n : ℝ) * alpha : ℂ)⁻¹ * ∑' st : ℤ × ℤ,
          wignerSign st.1 st.2 *
            f (alpha * j.val + n * alpha * st.2 / 2, Real.pi * st.1 / (n * alpha))) ∧
    (∀ f : SchwartzMap ℝ ℂ,
      Filter.Tendsto (fun M : ℕ => wignerQMean n alpha j M f) Filter.atTop
        (nhds (∑' k : ℤ, f (combSupportPoint n alpha j k))) ∧
      Filter.Tendsto (fun M : ℕ => wignerPMean n alpha M f) Filter.atTop
        (nhds (∑' k : ℤ, f (2 * Real.pi * k / (n * alpha))))) ∧
    (Finset.univ.filter (fun st : Fin 2 × Fin 2 =>
      wignerSign st.1.val st.2.val = -1)).card = 1 ∧
    (Finset.univ.filter (fun st : Fin 2 × Fin 2 =>
      wignerSign st.1.val st.2.val = 1)).card = 3 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
