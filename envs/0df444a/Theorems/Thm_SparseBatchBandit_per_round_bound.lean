-- Prove2me | Theorems.Thm_SparseBatchBandit_per_round_bound
-- name    : SparseBatchBandit.per_round_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:35:44.623268+00:00
-- url     : https://prove2.me/theorems/d0626860-67c5-443c-9c08-2f41aecb927f
-- title:
--   §4.2.3, p.18 — per-round regret bound
-- statement:
--   Under the standing hypotheses, let $m\in[M]$ and let $t$ be a round of batch $m$. At every outcome,
--
--   $$
--   \max_{a\in[K]}(x_{t,a}-x_{t,a_t})^\top\theta^\star\le\max_{a\in[K]}(x_{t,a}-x_{t,a_t})^\top(\theta^\star-\hat\theta_{m-1})\le2\max_{a\in[K]}\big|x_{t,a}^\top(\theta^\star-\hat\theta_{m-1})\big|,
--   $$
--
--   and with probability at least $1-T^{-3}$,
--
--   $$
--   2\max_{a\in[K]}\big|x_{t,a}^\top(\theta^\star-\hat\theta_{m-1})\big|\le6\sqrt{\log(TK)}\cdot\|\theta^\star-\hat\theta_{m-1}\|_2 .
--   $$
--
--   This turns an estimation error into an instantaneous regret bound.
--
--   Differences from the source:
--   - reading: Assumption 1's display, at unit v only → HasSubgaussianMGF of ⟨v, x⟩ with proxy 1, for every λ and unit v; reason: the unit-scale bound is not sub-Gaussianity; §2.1 and p.18 use every scale
--   - reading: O, Ω and Poly with numerical constants → ∀ A ε β p, ∃ constants, ∀ instance; reason: the implied constants of the hypotheses are the only reading under which a bound can hold: a constant uniform over them would allow d = exp(T)
--   - reading: b = Θ(√T (T/s₀)^(1/(2(2^M−1)))), t₁ = b√s₀, t_m = ⌊b√t_{m−1}⌋, t_M = T → exact b, floors on every t_m, each capped at T, last point T; reason: the page leaves b open up to Θ, and a grid point is a round; this b makes the unrounded recursion end exactly at T
--   - reading: each batch is partitioned into M intervals evenly → q-th round in T_m^(j) iff ⌊(j−1)n/M⌋ < q ≤ ⌊jn/M⌋; reason: the page gives no formula; this is the even floor partition
--   - reading: no statement on the joint law of contexts and noises → the context family is independent of the noise family; reason: the proof on p.28 conditions on the selected contexts and uses this
--   - reading: a* = argmax without a tie-break in Assumption 2 → lowest-index maximizer, the rule of Algorithm 1; reason: the proof applies Assumption 2 at θ̂₀ = 0, where all arms tie
--   - generalization: θ̂_m is the argmin → θ̂_m is the output of an arbitrary measurable selection of minimizers; reason: the argmin need not be unique; the statement covers every choice, so it specializes to any rule the paper could mean
--   - generalization: M = O(log log(T/s₀)) → M ≤ A max(1, log log(T/s₀)); reason: keeps the small instances with log log(T/s₀) ≤ 1; large instances are the paper's
--   - encoding: no explicit ranges → T ≥ 2, d ≥ 1, K ≥ 2, M ≥ 1, s₀ ≥ 1, γ, ρ > 0; reason: the formulas degenerate outside them: K = 1 gives log K = 0 and T = 1, d = 1 makes the right side 0
--   - encoding: vectors in ℝ^d, rounds 1..T → Fin d → ℝ with the published l2Norm; rounds Fin T, round t + 1 of the page being t; reason: Lean convention; same instances
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.2.3, p.18

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_action
import Definitions.Def_SparseBatchBandit_batch
import Definitions.Def_SparseBatchBandit_maxArm
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **Per-round regret bound**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.2.3, p.18 (PDF 18). Given `m ∈ [M]` and `t` in batch `m`,
at every point `ω`,
`max_a (x_{t,a} − x_{t,a_t})⊤θ⋆ ≤ max_a (x_{t,a} − x_{t,a_t})⊤(θ⋆ − θ̂_{m−1})
≤ 2 max_a |x_{t,a}⊤(θ⋆ − θ̂_{m−1})|`, and with probability at least `1 − T⁻³`,
`2 max_a |x_{t,a}⊤(θ⋆ − θ̂_{m−1})| ≤ 6 √(log(TK)) · ‖θ⋆ − θ̂_{m−1}‖₂`.

**Formalization Note.** `m − 1` is exact on `m ≥ 1`. -/
theorem per_round_bound (A ε β : ℝ) (p : ℕ)
    (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d)
    (_h : Standing A ε β p γ ρ P x ξ θstar sel) (m : ℕ) (_hm : m ∈ Finset.Icc 1 M) (t : Fin T) (_ht : t ∈ batch T s₀ M m) :
    (∀ ω : Ω,
      maxArm (fun a => (x ω t a - x ω t (action s₀ M sel (x ω) (ξ ω) θstar t)) ⬝ᵥ θstar) ≤
        maxArm (fun a => (x ω t a - x ω t (action s₀ M sel (x ω) (ξ ω) θstar t)) ⬝ᵥ
          (θstar - thetaHat s₀ M sel (x ω) (ξ ω) θstar (m - 1))) ∧
      maxArm (fun a => (x ω t a - x ω t (action s₀ M sel (x ω) (ξ ω) θstar t)) ⬝ᵥ
          (θstar - thetaHat s₀ M sel (x ω) (ξ ω) θstar (m - 1))) ≤
        2 * maxArm (fun a => |x ω t a ⬝ᵥ (θstar - thetaHat s₀ M sel (x ω) (ξ ω) θstar (m - 1))|)) ∧
    1 - ((T : ℝ) ^ 3)⁻¹ ≤
      P.real {ω |
        2 * maxArm (fun a => |x ω t a ⬝ᵥ (θstar - thetaHat s₀ M sel (x ω) (ξ ω) θstar (m - 1))|) ≤
          6 * Real.sqrt (Real.log ((T : ℝ) * K)) *
            HighDimProb.SparseRecovery.l2Norm (θstar - thetaHat s₀ M sel (x ω) (ξ ω) θstar (m - 1))} := by sorry

end SparseBatchBandit
