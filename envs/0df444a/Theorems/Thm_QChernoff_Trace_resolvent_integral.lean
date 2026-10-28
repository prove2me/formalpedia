-- Prove2me | Theorems.Thm_QChernoff_Trace_resolvent_integral
-- name    : QChernoff.Trace.resolvent_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:36.889669+00:00
-- url     : https://prove2.me/theorems/65c04aac-f23b-43a4-a068-182c3b115cc0
-- title:
--   Proof of Lemma 1, p. 4 — $A(A+x)^{-1}-B(B+x)^{-1}=\int_0^1 \frac{d}{dt}(B+t\Delta)(B+t\Delta+x)^{-1}dt=\int_0^1 x(B+t\Delta+x)^{-1}\Delta(B+t\Delta+x)^{-1}dt$
-- statement:
--   Let $H$ be a complex Hilbert space, $A,B\ge0$ positive bounded operators on $H$, $\Delta:=A-B$, and $x>0$ a real number. For $0\le t\le 1$ the operator $B+t\Delta=(1-t)B+tA$ is positive, so $B+t\Delta+x$ is invertible. Then
--
--   $$A(A+x)^{-1}-B(B+x)^{-1}=\int_0^1\frac{d}{dt}\Big[(B+t\Delta)(B+t\Delta+x)^{-1}\Big]dt=\int_0^1 x\,(B+t\Delta+x)^{-1}\,\Delta\,(B+t\Delta+x)^{-1}\,dt ,$$
--
--   both integrands being integrable operator-valued functions of $t$ on $[0,1]$.
--
--   This identity reduces the positivity of $\operatorname{Tr}[PB(A(A+x)^{-1}-B(B+x)^{-1})]$ in the proof of Lemma 1 to the positivity statement (10).
--
--   **Formalization Note** The integrals are interval integrals of functions $\mathbb R\to(H\to_L H)$; $t\Delta$ uses the real scalar action and the shift $x$ is $(x:\mathbb C)\cdot\mathbb 1$.
--
--   Differences from the source:
--   - generalization: operators of unspecified dimension → bounded positive operators on an arbitrary complex Hilbert space; reason: p. 3 states that the proof goes through in infinite dimensions; H = ℂⁿ is the matrix case
--   - encoding: the display, inside "for all x > 0" → x : ℝ with 0 < x as an explicit hypothesis; reason: the display is asserted for the x > 0 of the surrounding integral
--   - encoding: the chain A(A+x)⁻¹ − B(B+x)⁻¹ = (B+∆)(B+∆+x)⁻¹ − B(B+x)⁻¹ = ∫₀¹ dt d/dt(…) = ∫₀¹ dt x(…)∆(…) → the first step (B + ∆ = A) is not restated; the other two equalities are the two conjuncts, with d/dt as Mathlib's deriv and (·)⁻¹ as Ring.inverse; reason: B + (A − B) = A is an identity of the definitions; the function of τ is differentiable on a neighbourhood of [0, 1] because the invertible operators form an open set, so deriv is the true derivative and Ring.inverse the true inverse
--   - encoding: existence of the two integrals over [0, 1] (implicit in the display) → two explicit IntervalIntegrable conjuncts in the conclusion; reason: they assert that neither interval integral is Lean's junk value 0 of a non-integrable function; this makes the statement stronger, not weaker
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 4, unnumbered display in the proof of Lemma 1, Appendix A

import Mathlib

namespace QChernoff.Trace

/-- Proof of Lemma 1, Appendix A, p. 4: for `x > 0` and `Δ = A − B`, the resolvent difference
`A(A + x)⁻¹ − B(B + x)⁻¹` equals `∫₀¹ d/dt (B + tΔ)(B + tΔ + x)⁻¹ dt`, which in turn equals
`∫₀¹ x (B + tΔ + x)⁻¹ Δ (B + tΔ + x)⁻¹ dt`; both integrands are integrable on `[0, 1]`. -/
theorem resolvent_integral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B) (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable
        (deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)))
        MeasureTheory.volume 0 1 ∧
      IntervalIntegrable
        (fun t : ℝ => x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)))
        MeasureTheory.volume 0 1 ∧
      A * Ring.inverse (A + (x : ℂ) • 1) - B * Ring.inverse (B + (x : ℂ) • 1) =
        ∫ t in (0 : ℝ)..1,
          deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)) t ∧
      ∫ t in (0 : ℝ)..1,
          deriv (fun τ : ℝ => (B + τ • (A - B)) * Ring.inverse (B + τ • (A - B) + (x : ℂ) • 1)) t =
        ∫ t in (0 : ℝ)..1, x • (Ring.inverse (B + t • (A - B) + (x : ℂ) • 1) * (A - B) *
          Ring.inverse (B + t • (A - B) + (x : ℂ) • 1)) := by sorry

end QChernoff.Trace
