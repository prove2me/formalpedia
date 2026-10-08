-- Prove2me | Theorems.Thm_PalmQueueing_Loynes_coupling_convergence
-- name    : PalmQueueing.Loynes.coupling_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T23:41:29.661996+00:00
-- url     : https://prove2.me/theorems/d5c68d61-a2c5-4393-aa1f-e330e6e6ab17
-- title:
--   Theorem 2.4.1 — coupling implies convergence in variation
-- statement:
--   **Theorem 2.4.1.** If $\{X_n\}$ couples with a $\theta$-compatible sequence
--   $\{Z\circ\theta^n\}$, then the sequence $\{X_{n+k}\}_{n \ge 0}$ converges in variation to
--   $\{Z\circ\theta^n\}$ as $k$ tends to $\infty$:
--   $$ \lim_{k\to\infty} \big| \widetilde{P}_{X,k} - \widetilde{P}_{Z,k} \big| = 0 , \tag{2.4.1} $$
--   where $\widetilde{P}_{X,k}$ is the law of the whole shifted trajectory
--   $\widetilde{X}_k = (X_k, X_{k+1}, \dots)$ on the infinite product space.
--
--   The convergence is in variation **on the law of the entire trajectory**, not of a single
--   coordinate and not merely in distribution — which is what makes it the right notion of "reaches
--   the stationary regime". The book derives it from the **coupling inequality**
--   $$ |\widetilde{P}_{X,k} - \widetilde{P}_{Z,k}| \le P(N > k) , \tag{2.4.2} $$
--   obtained by splitting each event on $\{\widetilde{X}_k = \widetilde{Z}_k\}$; finiteness of the
--   coupling time $N$ then gives (2.4.1), with no further hypothesis. In particular, if $\{Z_n\}$ is
--   $\theta$-stationary, $|\widetilde{P}_{X,k} - \widetilde{P}_Z| \to 0$ (2.4.3).
--
--   The statement quantifies the measurable set inside the index, which is exactly the supremum
--   defining the distance in variation being small. $E$ is any measurable space: p.99 takes $(E,
--   \mathcal{E})$ Polish and introduces the metric $d_\infty$ on $E^\infty$ only to identify that
--   space's Borel field with the product $\sigma$-field, which is used directly here.
--
--   **Formalization Note.** The coupling time $N$ is an $\mathbb{N}$-valued random variable (measurable), and $X_n = Z_n$ for all $n \ge N$ holds $P$-almost surely.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 99, Theorem 2.4.1

import Mathlib
import Definitions.Def_PalmQueueing_Loynes_Coupling

/-!
# Theorem 2.4.1: coupling implies convergence in variation (§2.4.1, p.99)
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 2.4.1** (§2.4.1, p.99). If `{X_n}` couples with a `θ`-compatible sequence
`{Z ∘ θⁿ}`, then the sequence `{X_{n+k}}_{n ≥ 0}` converges in variation to `{Z ∘ θⁿ}` as `k`
tends to `∞`:

`(2.4.1)  lim_{k→∞} | P̃_{X,k} − P̃_{Z,k} | = 0`,

where `P̃_{X,k}` is the law on `(E^∞, E^∞)` of the whole shifted trajectory
`X̃_k = (X_k, X_{k+1}, …)`.

The convergence is **in variation on the law of the entire trajectory**, not of one coordinate and
not in distribution: `|P̃_{X,k} − P̃_{Z,k}| = sup_{C} |P̃_{X,k}(C) − P̃_{Z,k}(C)|` over all
measurable `C ⊆ E^∞`. That is why it is stated with the set quantified inside the index `K`, which
is exactly the supremum being small. The book derives it from the **coupling inequality**
`(2.4.2) |P̃_{X,k} − P̃_{Z,k}| ≤ P(N > k)`, which is finite-`N` plus nothing else.

`E` is any measurable space here. p.99 takes `(E, ℰ)` Polish with its Borel field and introduces
the metric `d_∞` on `E^∞` only to identify that space's Borel field with the product σ-field; the
statement uses the product σ-field directly, so the metric is not needed. -/
theorem coupling_convergence {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Ω) (X Z : ℕ → Ω → E)
    (hXmeas : ∀ n, Measurable (X n)) (hZmeas : ∀ n, Measurable (Z n))
    (hZcomp : IsShiftCompatible θ Z)
    (hcouple : Couple P X Z) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ C : Set (ℕ → E), MeasurableSet C →
        |(P {ω | (fun n : ℕ => X (n + k) ω) ∈ C}).toReal
          - (P {ω | (fun n : ℕ => Z (n + k) ω) ∈ C}).toReal| ≤ ε := by sorry

end PalmQueueing.Loynes
