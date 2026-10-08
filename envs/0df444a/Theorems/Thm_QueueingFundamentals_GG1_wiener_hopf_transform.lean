-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_wiener_hopf_transform
-- name    : QueueingFundamentals.GG1.wiener_hopf_transform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:48:40.857927+00:00
-- url     : https://prove2.me/theorems/b85488a7-f4a8-4679-934f-eed44549dafb
-- title:
--   Eqs. (6.10)–(6.12) — the Wiener–Hopf transform relation for the G/G/1 delay
-- statement:
--   Let $\nu$ be a stationary delay distribution of the G/G/1 queue with interarrival law $A$ and service law $B$, let $W_q$ be its CDF, $U$ the law of $S-T$, and define $W_q^-(t)=\int_{-\infty}^{t}W_q(t-x)\,dU(x)$ for $t<0$ and $W_q^-(t)=0$ for $t\ge0$ (6.10). Then
--
--   $$
--   W_q^-(t)+W_q(t)=\int_{-\infty}^{t}W_q(t-x)\,dU(x)\qquad(-\infty<t<\infty). \tag{6.11}
--   $$
--
--   Write $\bar W_q(s)=\int_{-\infty}^{\infty}e^{-st}W_q(t)\,dt$ and $\bar W_q^-(s)=\int_{-\infty}^{\infty}e^{-st}W_q^-(t)\,dt$ for the two-sided Laplace transforms, $A^*,B^*$ for the Laplace–Stieltjes transforms and $U^*(s)=\int e^{-sx}\,dU(x)$. For every complex $s$ with $\operatorname{Re}s>0$ and $\int e^{(\operatorname{Re}s)x}\,dA(x)<\infty$,
--
--   $$
--   U^*(s)=A^*(-s)B^*(s),\qquad \bar W_q^-(s)+\bar W_q(s)=\bar W_q(s)A^*(-s)B^*(s),
--   $$
--
--   and, whenever $A^*(-s)B^*(s)\ne1$,
--
--   $$
--   \bar W_q(s)=\frac{\bar W_q^-(s)}{A^*(-s)B^*(s)-1}. \tag{6.12}
--   $$
--
--   This is the transform form of Lindley's equation: it reduces the G/G/1 delay to the determination of $\bar W_q^-$.
--
--   **Formalization Note** The page does not say where the transforms converge. The strip used here, $0<\operatorname{Re}s$ with a finite exponential moment of $A$ at $\operatorname{Re}s$ (so that $A^*(-s)$ exists), is a labelled hypothesis; the division in (6.12) is stated only where its denominator is nonzero.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.285–286, Eqs. (6.10), (6.11), U*(s) = A*(−s)B*(s) and (6.12)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- Eqs. (6.10)–(6.12) (pp.285–286). Let `ν` be a stationary delay distribution of the G/G/1 queue
with interarrival law `A` and service law `B`, `W_q = cdfOf ν`, `U` the law of `S − T`, and
`W_q^−` as in (6.10). Then
(6.11) `W_q^−(t) + W_q(t) = ∫_{−∞}^{t} W_q(t − x) dU(x)` for all real `t`; and for every complex
`s` in the strip `0 < Re s` where `A` has the exponential moment `∫ e^{(Re s)x} dA(x) < ∞`
(a strip the page leaves implicit), `U^*(s) = A^*(−s)B^*(s)`,
`W̄_q^−(s) + W̄_q(s) = W̄_q(s)A^*(−s)B^*(s)`, and, when `A^*(−s)B^*(s) ≠ 1`,
(6.12) `W̄_q(s) = W̄_q^−(s)/(A^*(−s)B^*(s) − 1)`, with two-sided Laplace transforms `W̄`. -/
theorem wiener_hopf_transform (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsStationaryDelay A B ν) :
    (∀ t : ℝ, negPart (diffLaw A B) (cdfOf ν) t + cdfOf ν t =
        ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B)) ∧
    ∀ s : ℂ, 0 < s.re → Integrable (fun x : ℝ => Real.exp (s.re * x)) A →
      QueueingFundamentals.MG1.lst (diffLaw A B) s = QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ∧
      twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
        twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) ∧
      (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ≠ 1 →
        twoSidedLaplace (cdfOf ν) s =
          twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s / (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1)) := by sorry

end QueueingFundamentals.GG1
