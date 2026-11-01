-- Prove2me | Theorems.Thm_PSDPolyApprox_lemma_1
-- name    : PSDPolyApprox.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:44.421044+00:00
-- url     : https://prove2.me/theorems/efe76455-3a27-4ed4-9b15-ea5f4f393b18
-- title:
--   Lemma 1 — $\mu\{T_\rho f\ge4\}\le e^{-c\sqrt n}$ for $\rho=\sqrt{5/n}$, $f\ge0$, $\mathbb E f=1$, $\max f\le e^{\sqrt n}$
-- statement:
--   **Lemma 1.** There is an absolute constant $c>0$ such that the following holds for every $n$. Let $f:H_n\to\mathbb R$ satisfy $f\ge0$, $\mathbb E[f]=1$ and $\max f\le e^{\sqrt n}$, and let $\rho=\sqrt{5/n}$. Then
--   $$
--   \mu\{x\in H_n : (T_\rho f)(x)\ge4\}\le\exp(-c\sqrt n),
--   $$
--   where $\mu$ is the uniform probability measure on $H_n$.
--
--   This concentration estimate shows that a single nonnegative rank-one term of a factorization of (4) can witness the bound (7) only on an exponentially small fraction of the hypercube, as long as its row factor is not too spiked.
--
--   **Formalization Note** The constant $c$ is chosen before $n$ and $f$.
--
--   Differences from the source:
--   - reading: T_ρ defined for ρ ∈ [0, 1] → T_ρ given by the Fourier formula Σ_S ρ^{|S|} f̂(S) χ_S for every real ρ; reason: Lemma 1 takes ρ = √(5/n), which exceeds 1 for n < 5, so the printed statement needs T_ρ for ρ > 1; the Fourier formula is the paper's own definition and agrees with it on [0, 1]
--   - encoding: H_n = {−1, 1}^n and the uniform measure µ → functions Fin n → ℤˣ; µ(S) = |S|/2^n and E[f] = 2^{−n} Σ f; reason: ℤˣ = {±1}; same instances
--   - encoding: max f ≤ e^{√n} → f(x) ≤ e^{√n} for every x ∈ H_n; reason: H_n is finite and nonempty; same instances
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, Lemma 1, p.6

import Mathlib
import Definitions.Def_PSDPolyApprox_noise
import Definitions.Def_PSDPolyApprox_prob

namespace PSDPolyApprox

/-- **Lemma 1 (concentration of `T_ρ f`).**
Fawzi, arXiv:1811.09649v1, Lemma 1, p.6: "Assume f : Hn → R with f ≥ 0 such that E[f] = 1 and
max f ≤ e^{√n}. Assume ρ = √(5/n). Then µ{x ∈ Hn : (Tρf)(x) ≥ 4} ≤ exp(−c√n) for some absolute
constant c > 0."

There is an absolute `c > 0` such that for every `n` and every `f : Hₙ → ℝ` with `f ≥ 0`,
`E[f] = 1` and `max f ≤ e^{√n}`: `µ{x : T_{√(5/n)} f(x) ≥ 4} ≤ exp(−c√n)`.

**Formalization Note.** `c` is chosen before `n` and `f` (absolute constant). `T_ρ` is the Fourier
formula for every real `ρ`, so the statement covers `n < 5`, where `√(5/n) > 1`; at `n = 0`,
Lean's `√(5/0) = 0`. `µ` is the uniform probability (count over `2ⁿ`). -/
theorem lemma_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f : Cube n → ℝ), (∀ x, 0 ≤ f x) → expect f = 1 →
      (∀ x, f x ≤ Real.exp (Real.sqrt n)) →
      prob {x | 4 ≤ noise (Real.sqrt (5 / (n : ℝ))) f x} ≤
        Real.exp (-(c * Real.sqrt n)) := by sorry

end PSDPolyApprox
