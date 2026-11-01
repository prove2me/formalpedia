-- Prove2me | Theorems.Thm_PSDPolyApprox_lemma_1_general
-- name    : PSDPolyApprox.lemma_1_general
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:46.67055+00:00
-- url     : https://prove2.me/theorems/51e9621b-0c94-434d-af9f-4aef6cfbd304
-- title:
--   Lemma 1, as used on p.7 — $\mu\{T_\rho f\ge t\}\le e^{-c\sqrt n}$ for any $t>e$ and $\rho=\sqrt{\beta/n}$
-- statement:
--   For every $\beta>0$ and every threshold $t>e$ there is a constant $c>0$, depending only on $\beta$ and $t$, such that the following holds for every $n$. Let $f:H_n\to\mathbb R$ satisfy $f\ge0$, $\mathbb E[f]=1$ and $\max f\le e^{\sqrt n}$, and let $\rho=\sqrt{\beta/n}$. Then
--   $$
--   \mu\{x\in H_n : (T_\rho f)(x)\ge t\}\le\exp(-c\sqrt n).
--   $$
--   Lemma 1 is the case $\beta=5$, $t=4$. The proof of Theorem 1 applies the lemma with the threshold $t=3$ (p.7), and for general $\epsilon\in(0,1)$ it needs $\rho^2=\beta/n$ with $\beta$ depending on $\epsilon$ (p.6: "the proof works with any constant $0<\epsilon<1$").
--
--   **Formalization Note** The constant $c$ is chosen before $n$ and $f$.
--
--   Differences from the source:
--   - generalization: ρ = √(5/n) and threshold t = 4 (Lemma 1); t = 3 on p.7 → ρ = √(β/n) and threshold t for every β > 0 and t > e; reason: the paper invokes the lemma with t = 3 and states the proof works for every ε, which needs other β; specializes to Lemma 1 at β = 5, t = 4 and to the p.7 use at t = 3
--   - reading: T_ρ defined for ρ ∈ [0, 1] → T_ρ given by the Fourier formula Σ_S ρ^{|S|} f̂(S) χ_S for every real ρ; reason: Lemma 1 takes ρ = √(5/n), which exceeds 1 for n < 5, so the printed statement needs T_ρ for ρ > 1; the Fourier formula is the paper's own definition and agrees with it on [0, 1]
--   - encoding: H_n = {−1, 1}^n and the uniform measure µ → functions Fin n → ℤˣ; µ(S) = |S|/2^n and E[f] = 2^{−n} Σ f; reason: ℤˣ = {±1}; same instances
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, Lemma 1, p.6, as used on p.7 ("where we use t = 3 > e in the proof instead of t = 4") and p.6 ("the proof works with any constant 0 < ǫ < 1")

import Mathlib
import Definitions.Def_PSDPolyApprox_noise
import Definitions.Def_PSDPolyApprox_prob

namespace PSDPolyApprox

/-- **Lemma 1, general form (threshold `t > e`, noise `ρ = √(β/n)`).**
Fawzi, arXiv:1811.09649v1, p.7: "Using the concentration lemma (Lemma 1, where we use t = 3 > e
in the proof instead of t = 4) we know that for i ∈ Ic, µ{y : Tρfi(y) ≥ 3} ≤ exp(−c√n)", and
p.6: "it is easy to see that the proof works with any constant 0 < ǫ < 1".

For every `β > 0` and `t > e` there is `c > 0` such that for every `n` and every `f : Hₙ → ℝ`
with `f ≥ 0`, `E[f] = 1` and `max f ≤ e^{√n}`: `µ{x : T_{√(β/n)} f(x) ≥ t} ≤ exp(−c√n)`.
Lemma 1 is the case `β = 5`, `t = 4`.

**Formalization Note.** `c` depends on `β` and `t` only and is chosen before `n` and `f`. `T_ρ`
is the Fourier formula for every real `ρ` (`√(β/n) > 1` when `n < β`). -/
theorem lemma_1_general (β t : ℝ) (hβ : 0 < β) (ht : Real.exp 1 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : Cube n → ℝ), (∀ x, 0 ≤ f x) → expect f = 1 →
      (∀ x, f x ≤ Real.exp (Real.sqrt n)) →
      prob {x | t ≤ noise (Real.sqrt (β / (n : ℝ))) f x} ≤
        Real.exp (-(c * Real.sqrt n)) := by sorry

end PSDPolyApprox
