-- Prove2me | Theorems.Thm_TestScoreSubmod_eq_18
-- name    : TestScoreSubmod.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:42.08831+00:00
-- url     : https://prove2.me/theorems/51bfa7b0-234f-4798-bde5-5f79f3f86109
-- title:
--   Inequality (18): $u(A\cup\{i\})\ge(1-1/k)\,u(A)+a_i/k$
-- statement:
--   Let $0<k\le n=m+1$, let $g:\mathbb R_+^n\to\mathbb R_+$ be a measurable, symmetric, monotone submodular value function, and let $X_i\sim P_i$ be independent nonnegative performances whose $k$-fold replicas have integrable value.
--   Let $u(S)=\mathbb E[g(M_S(X))]$ and let $a_i$ be the replication test scores (7). For every set $A$ and every item $i\notin A$,
--
--   $$
--   u(A\cup\{i\})\ge\Bigl(1-\frac1k\Bigr)u(A)+\frac1k\,a_i .
--   $$
--
--   With $A=\{1,\dots,j-1\}$, $i=j$ and $a_j\ge a_1=\min_{i\in S}a_i$ this is (18), the step of the lower bound of Lemma 4 that the cascade iterates.
--
--   Differences from the source:
--
--   - generalization: A = {1,…,j − 1}, the item j, and a₁ = min_{i∈S} aᵢ, for j ∈ {1,…,k} → every A and every i ∉ A, with aᵢ in place of a₁; reason: (18) follows from aᵢ ≥ a₁; the Lean statement specializes to the source's
--   - generalization: stated inside the proof of Lemma 4, where g also has extended diminishing returns → no extended diminishing returns hypothesis; reason: not used by this step; the Lean statement specializes to the source's
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication scores aᵢ = E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁾,φ,…,φ)] of (7) → the k-fold replica y ↦ g(pad y) is integrable under the k-fold product of Pᵢ, for each i; reason: what (7) presupposes; integrability of every u(S) and of t ↦ g(z, t) follows from it and is not assumed
--   - encoding: N = {1,…,n} with 0 < k ≤ n; nonnegative independent Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → items Fin (m + 1) (n = m + 1); Pᵢ probability measures on ℝ≥0, independence as Measure.pi; g : (Fin (m+1) → ℝ≥0) → ℝ with 0 ≤ g x; reason: n ≥ 1 is forced by 0 < k ≤ n; same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Appendix D, proof of the lower bound of Lemma 4, (18), p.35

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_utility
import Definitions.Def_TestScoreSubmod_repScore

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Inequality (18)** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Appendix D, proof of the lower
bound of Lemma 4, (18), p.35: "u({1,…,j}) ≥ (1 − 1/k) u({1,…,j − 1}) + (1/k) a₁ for all
j ∈ {1,2,…,k}", with `a₁ = min{aᵢ | i ∈ S}`).

Let `0 < k ≤ n = m + 1`, `g` a nonnegative, measurable, symmetric, monotone submodular value
function, `Xᵢ ∼ Pᵢ` independent with integrable `k`-fold replicas, `u` the utility (4) and
`aᵢ` the replication test scores (7). For every set `A` and every item `i ∉ A`,

`u(A ∪ {i}) ≥ (1 − 1/k) u(A) + (1/k) aᵢ`.

**Formalization Note** The printed (18) is the case `A = {1,…,j−1}`, `i = j`, combined with
`aⱼ ≥ a₁`; it is stated here with the item's own score `aᵢ`. Extended diminishing returns is
not needed. `Measurable g` and the integrability of the `k` replicas are what the
expectations presuppose. `φ = 0`, performances in `ℝ≥0`. -/
theorem eq_18 {m k : ℕ} (hk : 0 < k) (hkn : k ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (P : Fin (m + 1) → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)]
    (hint : ∀ i, Integrable (fun y : Fin k → ℝ≥0 => g (pad y)) (Measure.pi fun _ : Fin k => P i))
    (A : Finset (Fin (m + 1))) (i : Fin (m + 1)) (hi : i ∉ A) :
    (1 - 1 / (k : ℝ)) * utility g P A + 1 / (k : ℝ) * repScore g P k i ≤
      utility g P (insert i A) := by sorry

end TestScoreSubmod
