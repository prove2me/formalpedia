-- Prove2me | Theorems.Thm_QZeroSum19_GK_expected_potential_le
-- name    : QZeroSum19.GK.expected_potential_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:16.707644+00:00
-- url     : https://prove2.me/theorems/3174dfd0-6f3c-4e1d-8837-4d72f7f5046e
-- title:
--   Proof of Lemma 1, p. 5 — after t iterations of Algorithm 1, E[Φ(t)] ≤ nm·e^{3Σ_{τ=1}^{t} η(τ)²}
-- statement:
--   Let $A\in[-1,1]^{n\times m}$ and let $\eta(1),\eta(2),\dots$ be step sizes with $0\le\eta(\tau)\le 1/2$ for every $\tau\ge1$. Run Algorithm 1 for $t$ iterations from $x_0=0$, $y_0=0$, and let $x_t,y_t$ be the iterates after $t$ updates. Then the expected potential satisfies
--   $$\mathbb E\Big[\Big(\sum_{j\in[m]}e^{-(A^{\mathsf T}x_t)_j}\Big)\Big(\sum_{i\in[n]}e^{(Ay_t)_i}\Big)\Big]\ \le\ nm\,\exp\Big(3\sum_{\tau=1}^{t}\eta(\tau)^2\Big).$$
--
--   The constant $nm$ is the initial potential $\Phi(0)$. This bound is what Markov's inequality is applied to in the proof of Lemma 1.
--
--   **Formalization Note** The expectation is over the sample-path law of the definition file. The page writes $\prod_{\tau=0}^{t-1}$ and $\sum_{\tau=0}^{t-1}$; under the index reading of Algorithm 1 adopted in the definition file (update $\tau$ uses step $\eta(\tau)$, $\tau\ge1$), these are $\prod_{\tau=1}^{t}$ and $\sum_{\tau=1}^{t}$, consistent with (3). The hypothesis $\eta(\tau)\le1/2$ is the one of the one-step bound.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 5, proof of Lemma 1, first display

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 5, first display: after `t` iterations of Algorithm 1 with steps
`η(τ) ∈ [0, 1/2]`, `E[Φ(t)] ≤ nm · e^{3 Σ_{τ=1}^{t} η(τ)²}`. -/
theorem expected_potential_le {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (η : ℕ → ℝ) (hη : ∀ τ, 1 ≤ τ → 0 ≤ η τ ∧ η τ ≤ 1 / 2) (t : ℕ) :
    expect A η t (fun ω => potential A (xAfter η ω t) (yAfter η ω t)) ≤
      (n : ℝ) * m * Real.exp (3 * ∑ τ ∈ Finset.Icc 1 t, η τ ^ 2) := by sorry

end QZeroSum19.GK
