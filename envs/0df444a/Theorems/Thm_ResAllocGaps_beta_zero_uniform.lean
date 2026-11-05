-- Prove2me | Theorems.Thm_ResAllocGaps_beta_zero_uniform
-- name    : ResAllocGaps.beta_zero_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:18.771923+00:00
-- url     : https://prove2.me/theorems/ca28e5f3-2a9c-4ca0-87d3-bd18ad29d3d6
-- title:
--   Proof of Theorem 1, $\beta=0$ — every online policy has regret $\Omega(\log T)$ for uniform abilities
-- statement:
--   Let the candidate abilities be uniform on $[0,1]$. There are a constant $c>0$ and a horizon $T_0$ such that for every $T\ge T_0$ there is a budget $B\in[T]$ for which every feasible online policy $\pi\in\Pi(B,T)$ (randomized policies allowed) satisfies
--   $$\mathrm{Regret}(B,T;\pi)\ \ge\ c\log T.$$
--   This is the $\beta=0$ clause of the universal lower bound; the paper obtains it from "Proposition 4 of Bray (2022)", the $\Omega(\log n)$ regret bound of that paper. In arXiv:1912.08917v6 this bound is Theorem 3 (Proposition 4 there is a different statement, about the dual prices), and its platform formalization is `OLPRegret.theorem_3` (deterministic policies, online linear program with $m$ resources). The present item is its case of one resource, unit consumption and uniform abilities, in this mission's model and for randomized policies.
--
--   **Formalization Note** $\log$ is the natural logarithm (the base only rescales $c$).
--
--   Differences from the source:
--   - reading: sup_{B∈[T]} Regret(B, T; π) with π ∈ Π(B, T) → ∃ B ∈ [1, T], ∀ π ∈ Π(B, T); reason: π depends on the B bound by the sup; over the finite set [T], 'for every family (π_B)_B, max_B Regret(B, T; π_B) ≥ bound' is equivalent by choice to 'some B has every π with Regret ≥ bound'
--   - encoding: Theorem 1 follows for β = 0 (for the uniform distribution) → ∃ c > 0, ∃ T₀, ∀ T ≥ T₀, … c · Real.log T ≤ regret π with μ = Lebesgue on [0, 1]; reason: the β = 0 clause of Theorem 1 with F the uniform law; natural log
--   - encoding: times t = 1, …, T; requests θ_t and seeds U_t; actions in {reject, accept}; Π(B, T) of p.8 → index t − 1 : Fin T; sample Fin T → ℝ × ℝ with law (μ ⊗ Unif[0,1])^{⊗T}; accept bits (Bool) measurable in the observed prefix; at most B acceptances almost surely (OnlinePolicy); reason: Lean convention; by Doob–Dynkin these are exactly the 𝓕_t-measurable actions of p.8, so the same policies
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Proof of Theorem 1, first paragraph, p.ec1 (citing Bray (2022), Proposition 4)

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy

open MeasureTheory

namespace ResAllocGaps

/-- **Theorem 1 for `β = 0`, uniform abilities** (Proof of Theorem 1, Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, Appendix EC.1, p.ec1): "For the uniform distribution over `[0, 1]`, we have that
`β = 0` and from Proposition 4 of Bray (2022), Theorem 1 follows for `β = 0`." For the uniform law
there are `c > 0` and `T₀` such that for every `T ≥ T₀` some budget `B ∈ [T]` makes every feasible
online policy pay regret at least `c log T`.

**Formalization Note.** Bray's result is posed on the platform as `OLPRegret.theorem_3` (online
linear program with `m` resources, deterministic non-anticipating policies); this statement is its
specialization to this mission's model (`m = 1`, unit consumption, `u ∼ Unif[0, 1]`) for randomized
online policies. `sup_{B ∈ [T]}` with a policy per budget is "some `B ∈ [1, T]` for which every
`π ∈ Π(B, T)`", which is equivalent over the finite set `[T]`. `log` is `Real.log`. -/
theorem beta_zero_uniform :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∃ B ∈ Finset.Icc 1 T,
      ∀ π : OnlinePolicy (volume.restrict (Set.Icc (0 : ℝ) 1)) T B,
        c * Real.log T ≤ regret π := by sorry

end ResAllocGaps
