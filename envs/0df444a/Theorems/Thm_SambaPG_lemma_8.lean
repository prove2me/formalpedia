-- Prove2me | Theorems.Thm_SambaPG_lemma_8
-- name    : SambaPG.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:40:28.510138+00:00
-- url     : https://prove2.me/theorems/147ebc15-8d32-4b0f-bdc3-61634ee22c34
-- title:
--   Lemma 8 — the regret identity $\mathcal Rg(T)=\sum_{a\neq a^\star}(r^\star-r_a)\,\mathbb E[\sum_{t<T}p_a(t)]$
-- statement:
--   Let the rewards $R_a(t)\in\{0,1\}$ have means $r_a$, with a unique optimal arm $a^\star$. Let $I(t)$ be the arm played at time $t$ by a policy whose choice is independent of that time's rewards: for every arm $a$ the indicator $I_a(t)$ is independent of $R_a(t)$. Let $p_a(t):=\mathbb E[I_a(t)\mid H(t-1)]$ for any $\sigma$-algebras $H(t-1)$. Then for every horizon $T$,
--
--   $$
--   \mathcal Rg(T)=r^\star T-\mathbb E\Big[\sum_{t=0}^{T-1}\sum_{a}I_a(t)R_a(t)\Big]=\sum_{a:a\neq a^\star}(r^\star-r_a)\,\mathbb E\Big[\sum_{t=0}^{T-1}p_a(t)\Big].
--   $$
--
--   The regret is the sum of the gaps weighted by the expected probability mass placed on suboptimal arms; this is the first step (19) of the proof of Theorem 1.
--
--   **Formalization Note** The policy is any arm process with the stated independence (a policy in the sense of §3.2 chooses from the past and an independent randomization, so it qualifies); for SAMBA, $p_a(t)$ is the SAMBA vector.
--
--   Differences from the source:
--
--   - generalization: a policy whose arm at t is a function of H(t − 1) and an independent uniform; p_a(t) := E[I_a(t) | H(t − 1)] → any arm process with {I(t) = a} independent of R_a(t), and p_a(t) the conditional expectation given any sub-σ-algebra H t; reason: every policy of §3.2 has this independence; only E[p_a(t)] = P(I(t) = a) enters
--   - encoding: rewards Bernoulli(r_a) → R_a(t) ∈ {0, 1} a.s. with P(R_a(t) = 1) = r_a, measurable; reason: the Bernoulli law spelled out
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Lemma 8, p.25 (proof p.26); eq. (5) and §3.2, p.7

import Mathlib
import Definitions.Def_SambaPG_regret

open MeasureTheory ProbabilityTheory

namespace SambaPG

/-- **Lemma 8 (regret identity, second equality of (5)).**
Denisov & Walton, arXiv:2007.10229v3, Lemma 8, p.25 (proof p.26); eq. (5) and §3.2, p.7.

Let `R_a(t) ∈ {0, 1}` be Bernoulli rewards with means `r_a`, and let `I(t)` be the arm played by a
policy at time `t`, with the event `{I(t) = a}` independent of the reward `R_a(t)` (the arm is chosen
from the past and an independent randomization, §3.2). For any σ-algebras `H(t − 1)`, put
`p_a(t) := E[I_a(t) | H(t − 1)]`. Then for every horizon `T`,
`Rg(T) = r⋆T − E[Σ_{t<T} Σ_a I_a(t) R_a(t)] = Σ_{a : a ≠ a⋆} (r⋆ − r_a) E[Σ_{t=0}^{T−1} p_a(t)]`.

**Formalization Note.** `Rg(T)` is the first expression of (5) (`SambaPG.policyRegret`). The
policy is any arm process whose choice at time `t` is independent of that time's rewards; the
σ-algebra `H t` stands for the paper's `H(t − 1)` and can be any sub-σ-algebra, since only
`E[p_a(t)] = P(I(t) = a)` enters. For SAMBA, `p_a(t)` is the SAMBA vector. -/
theorem lemma_8 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : ℕ → Ω → A → ℝ) (hRm : ∀ t a, Measurable fun ω => R t ω a)
    (hR01 : ∀ t a, ∀ᵐ ω ∂μ, R t ω a = 0 ∨ R t ω a = 1)
    (hRmean : ∀ t a, μ {ω | R t ω a = 1} = ENNReal.ofReal (B.r a))
    (I : ℕ → Ω → A) (hIm : ∀ t a, MeasurableSet {ω | I t ω = a})
    (hind : ∀ t a, IndepFun ({ω | I t ω = a}.indicator (1 : Ω → ℝ)) (fun ω => R t ω a) μ)
    (H : ℕ → MeasurableSpace Ω) (hH : ∀ t, H t ≤ MΩ) (T : ℕ) :
    policyRegret B μ R I T =
      ∑ a ∈ Finset.univ.erase B.aStar, (B.rStar - B.r a) *
        ∫ ω, ∑ t ∈ Finset.range T, (μ[{ω' | I t ω' = a}.indicator (1 : Ω → ℝ) | H t]) ω ∂μ := by sorry

end SambaPG
