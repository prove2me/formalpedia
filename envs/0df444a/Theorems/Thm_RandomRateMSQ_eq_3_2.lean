-- Prove2me | Theorems.Thm_RandomRateMSQ_eq_3_2
-- name    : RandomRateMSQ.eq_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:10.57866+00:00
-- url     : https://prove2.me/theorems/b8b716d0-7bed-46a2-99da-630f04678bae
-- title:
--   Display (3.2): pathwise decomposition of $\hat X^n$ (corrected: signs of the fifth and sixth terms)
-- statement:
--   Consider the $n$-th system on a path that satisfies the system equations, and let $\bar\mu$ be the mean of a measure $F$. Then for every $t\ge0$
--
--   $$
--   \hat X^n(t)=\hat X^n(0)+\hat A^n(t)+\frac{\lambda_nt-n\bar\mu t}{\sqrt n}-\hat M^n_1(t)+\frac{\sum_{k=1}^n\tilde\mu^n_k\int_0^tI^n_k(s)\,ds}{\sqrt n}-\hat\sigma^n t-\hat M^n_2(t)-\frac{\gamma\int_0^t(X^n(s)-n)^+ds}{\sqrt n},
--   $$
--
--   and the fifth term is the fairness mean times the scaled cumulative idleness:
--
--   $$
--   \frac{\sum_{k=1}^n\tilde\mu^n_k\int_0^tI^n_k(s)\,ds}{\sqrt n}=\langle\!\langle\iota,\eta^n_t\rangle\!\rangle\int_0^t\hat I^n(s)\,ds .
--   $$
--
--   This decomposition, with $\hat I^n=(\hat X^n)^-$, is the prelimit form of the limit equation (3.7).
--
--   **Formalization Note** The identity is pathwise algebra and holds for any constant $\bar\mu$. The mean is computed in $[0,\infty]$ and converted to a real number; it is finite for $t>\tau^n_0$, and for $t\le\tau^n_0$ both sides are $0$.
--
--   Differences from the source:
--   - correction: (3.2) with − Σₖ µ̃ⁿₖ∫₀ᵗIⁿₖ/√n (fifth term) and + Σₖ(µ̃ⁿₖt − µ̄t)/√n (sixth term) → + Σₖ µ̃ⁿₖ∫₀ᵗIⁿₖ/√n and − σ̂ⁿ t; reason: both signs are flipped by the algebra −Σₖ Dⁿₖ = −√n M̂ⁿ₁ − Σₖ µ̃ⁿₖ t + Σₖ µ̃ⁿₖ ∫₀ᵗ Iⁿₖ; counterexample n = 1, µ̃ = 1, λ₁ = 1, Xⁿ(0) = 0, no arrival before t = 1, γ = 0: X̂(1) = −1 while the printed right side is −3
--   - correction: second term (Aⁿ(t) − λₙ)/√n → Âⁿ(t) = (Aⁿ(t) − λₙ t)/√n; reason: typo: the third term (λₙt − nµ̄t)/√n and p.18's Âⁿ require λₙ t
--   - generalization: the decomposition (3.2) → (3.2) together with the identity Σₖ µ̃ⁿₖ∫₀ᵗIⁿₖ/√n = ⟨⟨ι, ηⁿₜ⟩⟩∫₀ᵗÎⁿ, and µ̄ the mean of any measure; reason: the identity is how the fifth term is used in the proof of Theorem 5 (p.19); dropping it gives (3.2); the algebra holds for every constant µ̄
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, eq. (3.2), p.6; the fifth term as ⟨⟨ι, ηⁿₜ⟩⟩∫Îⁿ in the proof of Theorem 5, p.19, and §3.2, p.9

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **Display (3.2)** (Büke–Qin, arXiv:1905.04198v1, p.6), with the signs of its fifth and sixth
terms corrected, and the identity behind the fifth term (p.9 and proof of Theorem 5, p.19).

On every path that satisfies the system equations of the `n`-th system, for every `t ≥ 0`:
`X̂ⁿ(t) = X̂ⁿ(0) + Âⁿ(t) + (λₙ t − nµ̄ t)/√n − M̂ⁿ₁(t) + Σₖ µ̃ⁿₖ ∫₀ᵗ Iⁿₖ/√n − σ̂ⁿ t − M̂ⁿ₂(t)
 − γ ∫₀ᵗ (Xⁿ − n)⁺/√n`, and `Σₖ µ̃ⁿₖ ∫₀ᵗ Iⁿₖ/√n = ⟨⟨ι, ηⁿₜ⟩⟩ ∫₀ᵗ Îⁿ`.

**Formalization Note (correction).** p.6 prints the fifth term with `−` and the sixth
(`Σₖ (µ̃ⁿₖ t − µ̄ t)/√n`) with `+`; both signs are wrong (n = 1, µ̃ = 1, λ₁ = 1, Xⁿ(0) = 0, no
arrival before `t = 1`, `γ = 0`: `X̂(1) = −1` while the printed right side is `−3`). It also prints
`(Aⁿ(t) − λₙ)/√n` for `Âⁿ(t) = (Aⁿ(t) − λₙ t)/√n`. `µ̄` may be the mean of any `F`: the identity
is pathwise algebra. -/
theorem eq_3_2 {Ω : Type*} {n : ℕ} (F : Measure ℝ≥0) (lam γ : ℝ) (ζ : ProbabilityMeasure ℝ≥0)
    (s : System Ω n) (ω : Ω) (hω : s.SystemEqs lam γ ω) (t : ℝ≥0) :
    Xhat s ω t = Xhat s ω 0 + Ahat lam s ω t + (lam * t - n * muBar F * t) / Real.sqrt n
      - M1hat s ω t
      + (∑ k, (s.rate k ω : ℝ) * cumInt (fun r => (s.I k ω r : ℝ)) t) / Real.sqrt n
      - sigmaHat F s ω * t - M2hat γ s ω t - γ * s.cumOverflow ω t / Real.sqrt n ∧
    (∑ k, (s.rate k ω : ℝ) * cumInt (fun r => (s.I k ω r : ℝ)) t) / Real.sqrt n =
      (meanRate (fairness ζ s ω t)).toReal * cumIhat s ω t := by sorry

end RandomRateMSQ
