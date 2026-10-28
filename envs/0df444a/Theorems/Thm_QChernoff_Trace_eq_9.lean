-- Prove2me | Theorems.Thm_QChernoff_Trace_eq_9
-- name    : QChernoff.Trace.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:40.008927+00:00
-- url     : https://prove2.me/theorems/c4a895d8-a54a-4e04-937e-50c48604c695
-- title:
--   Eq. (9), operator form — $A^t = \frac{\sin(t\pi)}{\pi}\int_0^\infty x^{t-1}A(A+x)^{-1}\,dx$ (corrected: $0 < t < 1$)
-- statement:
--   Let $H$ be a complex Hilbert space, $A\ge 0$ a positive bounded operator on $H$, and $0<t<1$. Then the integrand below is integrable on $(0,\infty)$ and
--
--   $$A^{t}=\frac{\sin(t\pi)}{\pi}\int_0^{+\infty}x^{t-1}\,A\,(A+x)^{-1}\,dx ,$$
--
--   where $(A+x)^{-1}$ is the inverse of $A+x\mathbb 1$ (which exists for $x>0$) and the integral is the Bochner integral of an operator-valued function, which converges absolutely in operator norm. For $H=\mathbb C$ this is the scalar identity $a^t=\frac{\sin(t\pi)}{\pi}\int_0^{\infty}\frac{a\,x^{t-1}}{a+x}\,dx$ for $a\ge0$.
--
--   In the proof of Lemma 1 this representation turns the difference $A^t-B^t$ into an integral of resolvent differences, which can then be handled one value of $x$ at a time.
--
--   **Formalization Note** `A ^ t` is Mathlib's `CFC.rpow`; real scalars act on operators through the real vector-space structure; `Ring.inverse` is the inverse in the ring of bounded operators.
--
--   Differences from the source:
--   - correction: valid for a ≥ 0 and 0 ≤ t ≤ 1 → 0 < t < 1; reason: at t = 0 and t = 1 the factor sin(tπ) vanishes while the integral diverges: for a = 1, t = 0 the left side is 1 and the right side is 0·∞ (in Lean a non-integrable integral is 0, so the printed range would be false)
--   - generalization: scalar a ≥ 0 (then "extending this representation to positive operators in the usual way") → positive bounded operator A on an arbitrary complex Hilbert space; reason: the paper uses the operator form; H = ℂ gives the scalar identity
--   - encoding: ∫_0^{+∞} dx a x^{t−1}/(a + x) → Bochner integral over Set.Ioi 0 of x^{t−1} • (A * Ring.inverse (A + x•1)) in H →L[ℂ] H; reason: for x > 0 the operator A + x is invertible, so Ring.inverse is the true inverse; the integrand is absolutely integrable, so the Lebesgue integral is the improper integral
--   - encoding: convergence of the integral (implicit in the display) → an explicit IntegrableOn conjunct in the conclusion; reason: it asserts that the Bochner integral is not Lean's junk value 0 of a non-integrable function; it makes the statement stronger, not weaker
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 4, eq. (9), proof of Lemma 1, Appendix A

import Mathlib

namespace QChernoff.Trace

/-- Eq. (9), p. 4, in the operator form used in Appendix A (corrected: `0 < t < 1`): the
integrand is Bochner integrable on `(0, ∞)` and `A ^ t = (sin(tπ)/π) ∫₀^∞ x^{t−1} A (A + x)⁻¹ dx`. -/
theorem eq_9 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1))) (Set.Ioi 0) ∧
      A ^ t = (Real.sin (t * Real.pi) / Real.pi) •
        ∫ x in Set.Ioi (0 : ℝ), x ^ (t - 1) • (A * Ring.inverse (A + (x : ℂ) • 1)) := by sorry

end QChernoff.Trace
