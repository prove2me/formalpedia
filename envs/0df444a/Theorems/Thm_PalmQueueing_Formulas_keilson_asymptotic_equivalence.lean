-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_keilson_asymptotic_equivalence
-- name    : PalmQueueing.Formulas.keilson_asymptotic_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:10:47.547132+00:00
-- url     : https://prove2.me/theorems/ea4534dc-f2c4-43ac-9738-0b05ee0376de
-- title:
--   Theorem 3.2.1 — the generalized Keilson asymptotic equivalence
-- statement:
--   **Theorem 3.2.1.** Let $F_n$ be a sequence of sets of $\mathcal{S}$ which are regular
--   w.r.t. $\{X(t)\}$ and such that $\tau^-(F_n)$ tends to infinity in probability w.r.t. $P$ as $n$
--   goes to $\infty$. Then the following generalization of Keilson's asymptotic equivalence (3.2.38)
--   holds:
--   $$ \frac{E^0_{F_n(\to A)}[\tau(F_n)]}{E^0_{F_n(\to A)}[T_1^{F_n(\to A)}]}
--   = P[\tau^-(F_n) \ge \tau^-(A)] \;\to_{n \to \infty}\; 1 , \tag{3.2.43} $$
--   so that
--   $$ E^0_{F_n(\to A)}[\tau(F_n)] \sim \Lambda_n^{-1} $$
--   where $\Lambda_n$ is the real number defined in Property 3.2.3 for $F = F_n$.
--
--   The generalization is from the countable-state Markov chain of Lemma 3.2.1 to a stationary
--   $\theta_t$-compatible process, with the cycle structure replaced by the thinning
--   $N^{F_n(\to A)}$ — the point process of first entrances into $A$ after $\{X(t)\}$ has left $F_n$.
--
--   Three parts, all stated. The **equality** in (3.2.43) is the substance: a ratio of Palm
--   expectations equals a stationary probability, which is what the exchange formula buys. The
--   **convergence to 1** is what the hypothesis on $\tau^-(F_n)$ delivers. And
--   $E^0_{F_n(\to A)}[\tau(F_n)] \sim \Lambda_n^{-1}$ is an **asymptotic equivalence**, stated as the
--   convergence of a ratio to $1$ and not as an equality.
--
--   $\Lambda_n$ enters through Property 3.2.3 — all the thinnings of $A$ and $F_n$ share one intensity
--   $\Lambda_n$ with $0 < \Lambda_n < \infty$ — together with
--   $E^0_{F_n(\to A)}[T_1^{F_n(\to A)}] = \Lambda_n^{-1}$, which is Eq. (1.2.27) of Chapter 1 applied
--   to the thinning.
--
--   **Formalization Note.** The standing assumptions of the stationary setting are hypotheses: $P$ is
--   $\theta_t$-invariant, $\{X(t)\}$ is $\theta_t$-compatible, $A$ and every $F_n$ are regular for
--   $\{X(t)\}$ and $A \cap F_n = \emptyset$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 209, Theorem 3.2.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Formulas_RareEvents

/-!
# Theorem 3.2.1: the generalized Keilson asymptotic equivalence (§3.2.6, p.209)
-/

namespace PalmQueueing.Formulas

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 3.2.1** (p.209). Let `F_n` be a sequence of sets of `S` which are regular with
respect to `{X(t)}` and such that `τ⁻(F_n)` tends to infinity in probability with respect to `P`
as `n` goes to `∞`. Then the following generalization of Keilson's asymptotic equivalence
`(3.2.38)` holds:

`(3.2.43)  E⁰_{F_n(→A)}[τ(F_n)] / E⁰_{F_n(→A)}[T_1^{F_n(→A)}] = P[τ⁻(F_n) ≥ τ⁻(A)] → 1`

so that `E⁰_{F_n(→A)}[τ(F_n)] ~ Λ_n^{-1}`, where `Λ_n` is the real number defined in Property
3.2.3 for `F = F_n`.

The generalization is from the countable-state Markov chain of Lemma 3.2.1 to a stationary
`θ_t`-compatible process, with the cycle structure replaced by the thinning `N^{F_n(→A)}` — the
point process of first entrances into `A` after `{X(t)}` has left `F_n`.

Three parts, all stated. The **equality** in (3.2.43) is the substance: a ratio of Palm
expectations equals a stationary probability, which is what the exchange formula buys. The
**convergence to 1** of that probability is what the hypothesis on `τ⁻(F_n)` delivers. And the
conclusion `E⁰_{F_n(→A)}[τ(F_n)] ~ Λ_n^{-1}` is an **asymptotic equivalence**, stated as the
convergence of the ratio to `1` and not as an equality.

`Λ_n` enters through Property 3.2.3, which gives that all the thinnings of `A` and `F_n` share one
intensity `Λ_n` with `0 < Λ_n < ∞`, together with `E⁰_{F_n(→A)}[T_1^{F_n(→A)}] = Λ_n^{-1}`; that
last identity is Eq. (1.2.27) of Chapter 1 applied to the thinning, and is carried as a
hypothesis.

The standing assumptions of the stationary setting (p.206) are hypotheses: `P` is `θ_t`-invariant,
`{X(t)}` is `θ_t`-compatible, `A` and every `F_n` are regular for `{X(t)}` (p.207: "All sets we use
will be assumed regular"), and `A` is disjoint from every `F_n`. -/
theorem keilson_asymptotic_equivalence {S : Type*} [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (θ : Flow Ω) (hinv : θ.Invariant P)
    (X : ℝ → Ω → S) (hXmeas : ∀ t, Measurable (X t)) (hXcomp : IsCompatible θ X)
    (A : Set S) (Fs : ℕ → Set S) (hdisj : ∀ n, Disjoint A (Fs n))
    (hregA : IsRegular P X A) (hregF : ∀ n, IsRegular P X (Fs n))
    (NFA : ℕ → PointProcess Ω)
    (hthin : ∀ n, IsRareEventThinning X A (Fs n) (NFA n))
    (P0 : ℕ → Measure Ω) (Lam : ℕ → ℝ)
    (hLam : ∀ n, 0 < Lam n)
    (hpalm : ∀ n, IsPalmProbability θ (NFA n) P (P0 n) (Lam n))
    (hmean : ∀ n, ∫ ω, (NFA n).T 1 ω ∂(P0 n) = (Lam n)⁻¹)
    (hrare : ∀ M : ℝ, Tendsto (fun n : ℕ => (P {ω | hitBwd X (Fs n) ω ≤ M}).toReal)
      atTop (𝓝 0)) :
    (∀ n : ℕ,
      (∫ ω, hitFwd X (Fs n) ω ∂(P0 n)) / (∫ ω, (NFA n).T 1 ω ∂(P0 n))
        = (P {ω | hitBwd X A ω ≤ hitBwd X (Fs n) ω}).toReal) ∧
    Tendsto (fun n : ℕ => (P {ω | hitBwd X A ω ≤ hitBwd X (Fs n) ω}).toReal) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (∫ ω, hitFwd X (Fs n) ω ∂(P0 n)) * Lam n) atTop (𝓝 1) := by sorry

end PalmQueueing.Formulas
