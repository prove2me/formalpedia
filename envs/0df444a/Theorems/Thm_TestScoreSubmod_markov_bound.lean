-- Prove2me | Theorems.Thm_TestScoreSubmod_markov_bound
-- name    : TestScoreSubmod.markov_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:44.121581+00:00
-- url     : https://prove2.me/theorems/abc253db-c2da-4d8d-8f9a-2cfd19610eda
-- title:
--   Markov step: $\Pr[g(Y_i)\ge c\,a]\le 1/c$
-- statement:
--   Let $k=r+1\le n=m+1$, let $g:\mathbb R_+^n\to\mathbb R_+$ be measurable and monotone, and let $P_i$ be a probability law on $\mathbb R_+$ under which the $k$-fold replica has integrable value. Let $Y_i$ be a vector of $k-1$ independent replicas of $X_i\sim P_i$ and let $a_i$ be the replication test score (7). If $c>1$, $a>0$ and $a_i\le a$, then
--
--   $$
--   \Pr\bigl[g(Y_i)\ge c\,a\bigr]\le\frac1c .
--   $$
--
--   With $a=a_k$, the largest score of the set, this gives $\Pr[g(Y_i)\le c\,a_k]\ge1-1/c$, which turns (29) into (30); $c=2$ yields the constant $4$ of Lemma 4.
--
--   Differences from the source:
--
--   - reading: "ai ≥ ak for all i ∈ {1,2,…,k}" (p.38) → aᵢ ≤ a; reason: typo: the ordering a₁ ≤ a₂ ≤ … ≤ a_k fixed on p.36 gives aᵢ ≤ a_k, which the Markov chain uses
--   - generalization: a = a_k, g symmetric, submodular, with extended diminishing returns → any a ≥ aᵢ with a > 0; g only nonnegative, measurable and monotone; reason: not used by this step; the Lean statement specializes to the source's
--   - encoding: division by c a_k → 0 < a; reason: the printed bound is undefined when c a_k = 0
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication score aᵢ of (7) with k = r + 1 replicas → the (r + 1)-fold replica y ↦ g(pad y) is integrable; reason: what (7) presupposes; the integrability of the other expectations follows from it
--   - encoding: k replicas, k − 1 replicas, 0 < k ≤ n; nonnegative Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → k = r + 1 with r + 1 ≤ m + 1 = n; Pᵢ a probability measure on ℝ≥0; replicas as Measure.pi over Fin r; 0 ≤ g x; reason: avoids natural-number subtraction k − 1; same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Appendix D, proof of step (d) of the upper bound of Lemma 4, p.38

import Mathlib
import Definitions.Def_TestScoreSubmod_repScore

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **The Markov step** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Appendix D, proof of (d),
p.38: "Pr[g(Yᵢ) ≥ c a_k] ≤ E[g(Yᵢ)]/(c a_k) ≤ E[g(Yᵢ, Xᵢ)]/(c a_k) ≤ 1/c").

Let `k = r + 1 ≤ n = m + 1`, `g` a nonnegative, measurable, monotone value function, `Pᵢ` a
probability law on `ℝ₊` with integrable `k`-fold replica, and `Yᵢ` a vector of `k − 1`
independent replicas of `Xᵢ ∼ Pᵢ`. If `c > 1`, `a > 0` and the replication score satisfies
`aᵢ ≤ a`, then

`Pr[g(Yᵢ) ≥ c a] ≤ 1/c`.

**Formalization Note** In the paper `a = a_k`, the largest score in `S` (p.38 prints
"aᵢ ≥ a_k", read as `aᵢ ≤ a_k` per the ordering on p.36). `g(Yᵢ)` is `g (pad Yᵢ)`, `φ = 0`.
Symmetry and submodularity of `g` are not needed for this step. -/
theorem markov_bound {m r : ℕ} (hr : r + 1 ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hmono : Monotone g)
    (P : Fin (m + 1) → Measure ℝ≥0) (i : Fin (m + 1)) [IsProbabilityMeasure (P i)]
    (hint : Integrable (fun y : Fin (r + 1) → ℝ≥0 => g (pad y))
      (Measure.pi fun _ : Fin (r + 1) => P i))
    (c a : ℝ) (hc : 1 < c) (ha : 0 < a) (hscore : repScore g P (r + 1) i ≤ a) :
    ((Measure.pi fun _ : Fin r => P i) {Y | c * a ≤ g (pad Y)}).toReal ≤ 1 / c := by sorry

end TestScoreSubmod
