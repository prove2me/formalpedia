-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_theorem_3_5_time_of_pair
-- name    : SampleMLS.ExpMoment.theorem_3_5_time_of_pair
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:51:30.853772+00:00
-- url     : https://prove2.me/theorems/acaf6f4d-b2ee-4154-92d4-38d0d363d3b0
-- title:
--   Theorem 3.5(i), proof — under (2), m_{t,θ}2^{θ+1} ≤ (2M_{t,θ}+1)2^{θ+1} ≤ 16κΓ(Θ+1)2^{ψn} + 2^{Θ+1} and 2^Θ ≤ 8Γ2^{ψn}
-- statement:
--   Let $\psi\ge0$, $\Gamma\ge1$, $\kappa>0$, $n,k\ge0$, and let the integer cap $\Theta$ and the trial counts $m_{t,\theta}$ satisfy (2): $x+1\le\Theta\le x+3$ with $x=\psi n+\log_2\Gamma$, and $M_{t,\theta}\le m_{t,\theta}\le 2M_{t,\theta}+1$ with $M_{t,\theta}=4\kappa\Gamma(\Theta+1)2^{\psi n-\theta}$, for $t\in\{0,\dots,k\}$ and $\theta\in\{0,\dots,\Theta\}$. Then for every such pair $(t,\theta)$
--   $$m_{t,\theta}2^{\theta+1}\le(2M_{t,\theta}+1)2^{\theta+1}\le16\kappa\Gamma(\Theta+1)2^{\psi n}+2^{\Theta+1},$$
--   moreover $2^\Theta\le8\Gamma2^{\psi n}$, and the trials of Algorithm 3.4 are those of the $(k+1)(\Theta+1)$ pairs: their number is $\sum_{t=0}^{k}\sum_{\theta=0}^{\Theta}m_{t,\theta}$.
--
--   Differences from the source:
--   - reading: m_{t,θ}2^{θ+1}N^{O(1)} ≤ (2M_{t,θ}+1)2^{θ+1}N^{O(1)} ≤ (16κΓ(Θ+1)2^{ψn} + 2^{Θ+1})N^{O(1)} → the same chain without the common factor N^{O(1)}; reason: one polynomial factor multiplies every term of the chain; the content is the inequality of the coefficients
--   - reading: "There are (k + 1)(Θ + 1) pairs" → the number of trials in trialList k Θ m is the sum of m_{t,θ} over the (k+1)(Θ+1) pairs t ∈ {0,…,k}, θ ∈ {0,…,Θ}; reason: the sentence counts the pairs whose trials make up the loop; the Lean states it for the loop it formalizes
--   - encoding: integer trial counts m_{t,θ} → m : ℕ → ℤ → ℕ; reason: (2) forces m_{t,θ} ≥ M_{t,θ} > 0
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), proof of Theorem 3.5(i), p. 18 (PDF 20)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Proof of Theorem 3.5(i), p. 18 (PDF 20): under (2), for every pair `(t, θ)`,
`m_{t,θ} 2^{θ+1} ≤ (2M_{t,θ} + 1) 2^{θ+1} ≤ 16κΓ(Θ + 1) 2^{ψn} + 2^{Θ+1}`, and
`Θ ≤ ψn + log Γ + 3` gives `2^Θ ≤ 8Γ 2^{ψn}`; the trials are those of the `(k + 1)(Θ + 1)` pairs. -/
theorem theorem_3_5_time_of_pair (ψ Γ κ : ℝ) (n k : ℕ) (Θ : ℤ) (m : ℕ → ℤ → ℕ)
    (hψ : 0 ≤ ψ) (hΓ : 1 ≤ Γ) (hκ : 0 < κ) (h2 : Cond2 ψ Γ κ n k Θ m) :
    (∀ t ≤ k, ∀ θ : ℤ, 0 ≤ θ → θ ≤ Θ →
      (m t θ : ℝ) * (2 : ℝ) ^ (θ + 1) ≤ (2 * Mtt κ Γ ψ n Θ θ + 1) * (2 : ℝ) ^ (θ + 1) ∧
      (2 * Mtt κ Γ ψ n Θ θ + 1) * (2 : ℝ) ^ (θ + 1) ≤
        16 * κ * Γ * ((Θ : ℝ) + 1) * (2 : ℝ) ^ (ψ * (n : ℝ)) + (2 : ℝ) ^ (Θ + 1)) ∧
    (2 : ℝ) ^ Θ ≤ 8 * Γ * (2 : ℝ) ^ (ψ * (n : ℝ)) ∧
    (trialList k Θ m).length =
      ∑ t ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (Θ.toNat + 1), m t (j : ℤ) := by sorry

end SampleMLS.ExpMoment
