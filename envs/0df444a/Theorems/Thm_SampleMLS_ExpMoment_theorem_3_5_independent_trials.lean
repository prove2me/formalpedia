-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_theorem_3_5_independent_trials
-- name    : SampleMLS.ExpMoment.theorem_3_5_independent_trials
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:51:42.902121+00:00
-- url     : https://prove2.me/theorems/88806e4b-43ce-400a-91b8-a170fd9d034c
-- title:
--   Theorem 3.5(iii), proof — m ≥ M_{t,θ} ≥ κ/p independent trials all fail with probability ≤ (1−p)^m ≤ e^{−pm} ≤ e^{−κ}
-- statement:
--   Let $\psi\ge0$, $\Gamma\ge1$, $\kappa>0$, integers $0\le\theta\le\Theta$, $n=|U|$, and $p\le1$ with $p\ge 2^{\theta-\psi n}/(4\Gamma(\Theta+1))$. Consider a trial of the pair $(t,\theta)$ of Algorithm 3.4 (draw $X$ uniformly from $\binom{U}{t}$; succeed iff $g(X)\le\theta$ and the extension call accepts $X$) that succeeds with probability at least $p$, and $m\ge M_{t,\theta}=4\kappa\Gamma(\Theta+1)2^{\psi n-\theta}$ trials of it. Then $M_{t,\theta}\ge\kappa/p$, the $m$ independent trials all fail with probability at most $(1-p)^m$, and $(1-p)^m\le e^{-pm}\le e^{-\kappa}$.
--
--   Differences from the source:
--   - generalization: a trial of the pair (t, θ) draws X ∈ (S choose t) with g ≤ θ with probability p = q_θ/C(n,t), and then A accepts → any trial law of the pair whose success probability is at least p, for any p ≤ 1 with p ≥ 2^{θ−ψn}/(4Γ(Θ+1)); reason: the step uses only these two facts; it specializes to the source with p = q_θ/C(n,t), which is ≤ 1 and satisfies the lower bound by the good-threshold milestone
--   - encoding: m_{t,θ} independent trials of the pair (t, θ) → loopLaw of List.replicate m (t, θ), the law of m independent copies of trialLaw; reason: the same independent trials
--   - encoding: integer trial count m_{t,θ} → m : ℕ; reason: (2) forces m_{t,θ} ≥ M_{t,θ} > 0
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), proof of Theorem 3.5(iii), p. 19 (PDF 21)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Proof of Theorem 3.5(iii), p. 19 (PDF 21): if a trial succeeds with probability at least `p`,
where `p ≤ 1` and `p ≥ 2^{θ−ψn}/(4Γ(Θ + 1))`, and `m ≥ M_{t,θ}`, then `M_{t,θ} ≥ κ/p`, the
`m` independent trials of the pair all fail with probability at most `(1 − p)^m`, and
`(1 − p)^m ≤ e^{−pm} ≤ e^{−κ}`. -/
theorem theorem_3_5_independent_trials (U : Finset ℕ) (gk : Finset ℕ → ℝ)
    (acc : Finset ℕ → Prop) (t : ℕ) (ψ Γ κ : ℝ) (Θ θ : ℤ) (p : ℝ) (m : ℕ)
    (hψ : 0 ≤ ψ) (hΓ : 1 ≤ Γ) (hκ : 0 < κ) (hθ : 0 ≤ θ) (hθΘ : θ ≤ Θ)
    (hp : (2 : ℝ) ^ ((θ : ℝ) - ψ * (U.card : ℝ)) / (4 * Γ * ((Θ : ℝ) + 1)) ≤ p) (hp1 : p ≤ 1)
    (htrial : p ≤ (trialLaw U gk acc t θ true).toReal)
    (hm : Mtt κ Γ ψ U.card Θ θ ≤ (m : ℝ)) :
    κ / p ≤ Mtt κ Γ ψ U.card Θ θ ∧
    (loopLaw U gk acc (List.replicate m (t, θ)) false).toReal ≤ (1 - p) ^ m ∧
    (1 - p) ^ m ≤ Real.exp (-(p * (m : ℝ))) ∧
    Real.exp (-(p * (m : ℝ))) ≤ Real.exp (-κ) := by sorry

end SampleMLS.ExpMoment
