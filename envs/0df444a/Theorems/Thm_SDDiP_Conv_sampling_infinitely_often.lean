-- Prove2me | Theorems.Thm_SDDiP_Conv_sampling_infinitely_often
-- name    : SDDiP.Conv.sampling_infinitely_often
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:48:49.146895+00:00
-- url     : https://prove2.me/theorems/373cb5be-9e0c-4173-8d91-2899fa10d0ff
-- title:
--   Proof of Claim 2 — with sampling with replacement, every scenario is sampled again with probability one
-- statement:
--   Suppose that in every iteration $M\ge 1$ scenarios are sampled with replacement: on a probability space $(\Omega,\mathcal F,\mathbb P)$ the draws $S_{i,k}$ ($i\in\mathbb N$, $k = 1,\dots,M$) are mutually independent random scenarios with $\mathbb P(S_{i,k} = n) = p_n$ for every scenario $n\in S_T$. Then with probability one every scenario is sampled in infinitely many iterations:
--   $$\mathbb P\Big(\forall n\in S_T\ \ \forall j\ \ \exists i\ge j\ \ \exists k:\ S_{i,k} = n\Big) = 1 .$$
--
--   In the proof of Claim 2 this guarantees that a scenario containing the node at which the approximation is not exact is sampled again after finitely many iterations.
--
--   **Formalization Note** The positivity $p_n > 0$ of the scenario probabilities is part of the model.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 476, proof of Claim 2

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage MeasureTheory

/-- Proof of Claim 2, p. 476 (Zou–Ahmed–Sun 2019): when the sampling is done with replacement
(independent draws from `{p_n : n ∈ S_T}`, `M ≥ 1` scenarios per iteration), with probability one every
scenario is sampled again after any iteration, i.e. every scenario is sampled in infinitely many
iterations. -/
theorem sampling_infinitely_often {H d ℓ M : ℕ} (D : Model H d ℓ) (hM : 0 < M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S) :
    ∀ᵐ ω ∂P, ∀ n : D.Leaf, ∀ j : ℕ, ∃ i ≥ j, ∃ k, S i ω k = n := by sorry

end SDDiP.Conv
