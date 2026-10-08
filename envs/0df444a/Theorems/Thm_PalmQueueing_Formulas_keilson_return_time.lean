-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_keilson_return_time
-- name    : PalmQueueing.Formulas.keilson_return_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:07:26.973029+00:00
-- url     : https://prove2.me/theorems/0f288b8d-2589-4ed0-9030-82c430e26229
-- title:
--   Lemma 3.2.1 — a closed form for the mean excursion-and-return time
-- statement:
--   **Lemma 3.2.1.** Let $f(x) = P_x(\tau(\alpha) < \tau(F))$ denote the probability that,
--   starting from $x \in F^c$, $X$ hits $\alpha$ before $F$. Then
--   $$ E_\alpha R = \Big(\sum_{y \in F} \pi(y) \sum_{x \in F^c} K(y,x) f(x)\Big)^{-1}
--   = \Big(\pi(\alpha) \sum_{x \ne \alpha} K(\alpha,x)(1 - f(x))\Big)^{-1} . \tag{3.2.39} $$
--
--   **Both expressions are asserted, and their equality is part of the content.** The first counts the
--   rate at which the chain leaves $F$ and then reaches $\alpha$ before returning to $F$; the second
--   counts the rate at which it leaves $\alpha$ and reaches $F$ before returning to $\alpha$. That
--   these two rates coincide is the cycle identity the lemma rests on, and stating only one of them
--   would drop half of it.
--
--   Why it matters: Keilson's asymptotic equivalence (3.2.38) says the extra return time back to
--   $\alpha$ after reaching $F$ is asymptotically negligible, and "the interest of this equivalence
--   comes from the fact that there is a simple expression for $E_\alpha R$", which is this.
--
--   **Formalization Note.** The chain is characterised by its initial law $P_x(X_0 = x) = 1$ and the
--   Markov property along finite paths; it is irreducible and $F$ is non-empty. Hitting times are
--   counted from time $0$, $\tau(E) = \inf\{n \ge 0 ; X_n \in E\}$, so that $f(\alpha) = 1$ and
--   $f(x) = 0$ for $x \in F$: this is the convention under which both expressions of (3.2.39) hold (the
--   second sum runs over $x \in F$ too). $R \ge 1$ is counted from time $1$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 205, Lemma 3.2.1

import Mathlib
import Definitions.Def_PalmQueueing_Formulas_RareEvents

/-!
# Lemma 3.2.1: a closed form for the mean excursion-and-return time (§3.2.5, p.205)
-/

namespace PalmQueueing.Formulas

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 3.2.1** (p.205). Let `{X(t)}` be an irreducible discrete-time Markov chain on a
countable state space with transition matrix `K` and stationary probability `π`, `α` a fixed
origin, and `F` a rarely visited set not containing it. Let `R ≥ 1` be the first return time to
`α` having first made an excursion to `F`, and let `f(x) = P_x(τ(α) < τ(F))` be the probability
that, starting from `x ∈ F^c`, `X` hits `α` before `F`. Then

`(3.2.39)  E_α R = ( Σ_{y ∈ F} π(y) Σ_{x ∈ F^c} K(y,x) f(x) )^{-1}
                 = ( π(α) Σ_{x ≠ α} K(α,x) (1 − f(x)) )^{-1}`.

Hitting times are counted from time `0`: `τ(E) = inf{n ≥ 0 ; X(n) ∈ E}`. That is the convention
under which the page's two expressions are correct: starting from `x = α` the chain has hit `α`
before `F`, so `f(α) = 1`, and starting from `x ∈ F` it has hit `F` first, so `f(x) = 0` — the
second sum runs over every `x ≠ α`, including `x ∈ F`, and needs exactly that value. (With hitting
times counted from `1`, the two-state chain `α ⇄ y`, `F = {y}`, has `E_α R = 2` while the first
expression is `0⁻¹`.) `R ≥ 1` is still a return time, counted from `1`.

**Both expressions are asserted, and their equality is part of the content.** The first counts
the rate at which the chain leaves `F` and then reaches `α` before returning to `F`; the second
counts the rate at which it leaves `α` and reaches `F` before returning to `α`. That these two
rates coincide is the cycle identity the lemma rests on, and stating only one of them would drop
half of it.

Why the lemma matters: Keilson's asymptotic equivalence `(3.2.38)`,
`lim_{π(F) → 0} E_α R / E_α τ(F) = 1`, says the extra return time back to `α` after reaching `F`
is asymptotically negligible — it takes so long to get to `F` that the tail of the cycle does not
matter. The interest of that equivalence "comes from the fact that there is a simple expression
for `E_α R`", which is this. -/
theorem keilson_return_time {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (C : RareEventChain S) (Px : S → Measure Ω) (hPx : ∀ x, IsProbabilityMeasure (Px x))
    (X : ℕ → Ω → S) (hXmeas : ∀ n, Measurable (X n))
    (hstart : ∀ x, Px x {ω | X 0 ω = x} = 1)
    (hmarkov : ∀ (x : S) (n : ℕ) (p : ℕ → S) (z : S),
      Px x {ω | (∀ i ≤ n, X i ω = p i) ∧ X (n + 1) ω = z}
        = ENNReal.ofReal (C.K (p n) z) * Px x {ω | ∀ i ≤ n, X i ω = p i})
    (hit : Set S → Ω → ℕ)
    (hhit : ∀ (E : Set S) (ω : Ω), hit E ω = sInf {n : ℕ | X n ω ∈ E})
    (R : Ω → ℕ)
    (hR : ∀ ω, R ω = sInf {n : ℕ | 1 ≤ n ∧ X n ω = C.alpha ∧ ∃ m, 1 ≤ m ∧ m < n ∧ X m ω ∈ C.F})
    (f : S → ℝ)
    (hf : ∀ x : S, f x = (Px x {ω | hit {C.alpha} ω < hit C.F ω}).toReal)
    (ER : ℝ) (hER : ER = ∫ ω, (R ω : ℝ) ∂(Px C.alpha)) :
    ER = (∑' y : ↥C.F, C.pi y * ∑' x : ↥(C.Fᶜ), C.K y x * f x)⁻¹ ∧
    ER = (C.pi C.alpha * ∑' x : {x : S // x ≠ C.alpha}, C.K C.alpha x * (1 - f x))⁻¹ := by sorry

end PalmQueueing.Formulas
