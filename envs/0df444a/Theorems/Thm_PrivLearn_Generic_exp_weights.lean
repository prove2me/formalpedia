-- Prove2me | Theorems.Thm_PrivLearn_Generic_exp_weights
-- name    : PrivLearn.Generic.exp_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:01.407123+00:00
-- url     : https://prove2.me/theorems/622bd5bd-4b25-47ad-8d50-c725c12c2ed6
-- title:
--   Proof of Theorem 3.4, p. 12 — $\mathcal A^\varepsilon_q$ outputs $h$ with $\mathrm{err}_T(h)\ge \mathrm{OPT}+2\rho$ w.p. at most $|\mathcal H_d|e^{-\varepsilon n\rho/2}$
-- statement:
--   Let $X$ be a finite set of examples, $P$ a probability distribution on $X\times\{0,1\}$, $H$ a finite nonempty class of hypotheses with $\mathrm{OPT}=\min_{f\in H}\mathrm{err}(f)$, and let $\varepsilon>0$, $\rho>0$. Let $z$ be a database of $n$ labeled examples such that $|\mathrm{err}(h)-\mathrm{err}_T(h)|<\rho$ for every $h\in H$. Then
--
--   $$\Pr\big[\mathcal A^{\varepsilon}_q(z)=h \text{ for some } h \text{ with } \mathrm{err}_T(h)\ge \mathrm{OPT}+2\rho\big]\le |H|\exp(-\varepsilon n\rho/2).$$
--
--   The probability is over the coins of the mechanism only; the database is fixed. Together with the uniform convergence bound this gives the utility half of Theorem 3.4.
--
--   **Formalization Note.** The statement is pointwise in the database $z$: the conditioning on the uniform-convergence event in the paper is expressed as a hypothesis on $z$.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 12, proof of Theorem 3.4, display and the sentence 'Hence, the probability that A^ε_q(z) outputs ...'

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Generic_ExpMech

open MeasureTheory

namespace PrivLearn.Generic

/-- Proof of Theorem 3.4 (p. 12): on a database `z` with `|err(h) − err_T(h)| < ρ` for all
`h ∈ H`, the probability that `A^ε_q(z)` outputs a hypothesis with `err_T(h) ≥ OPT + 2ρ` is at
most `|H| exp(−εnρ/2)`. -/
theorem exp_weights {X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (H : Finset (X → Bool)) (hH : H.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (z : Fin n → X × Bool)
    (hz : ∀ h ∈ H, |err P h - errT z h| < ρ) :
    expMech H ε z {h | OPT P H hH + 2 * ρ ≤ errT z h}
      ≤ ENNReal.ofReal (H.card * Real.exp (-ε * n * ρ / 2)) := by sorry

end PrivLearn.Generic
