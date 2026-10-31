-- Prove2me | Theorems.Thm_TestScoreSubmod_lemma_4_lower
-- name    : TestScoreSubmod.lemma_4_lower
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:58.600189+00:00
-- url     : https://prove2.me/theorems/505e6d6b-0d9b-4654-ac9d-2fa54761a77c
-- title:
--   Cascade: $u(S)\ge(1-(1-1/k)^k)\min_{i\in S}a_i\ge(1-1/e)\min_{i\in S}a_i$
-- statement:
--   Let $0<k\le n=m+1$, let $g:\mathbb R_+^n\to\mathbb R_+$ be a measurable, symmetric, monotone submodular value function, and let $X_i\sim P_i$ be independent nonnegative performances whose $k$-fold replicas have integrable value.
--   Let $u(S)=\mathbb E[g(M_S(X))]$ and let $a_i$ be the replication test scores (7). For every set $S$ with $|S|=k$,
--
--   $$
--   \Bigl(1-\frac1e\Bigr)\min_{i\in S}a_i\;\le\;\Bigl(1-\Bigl(1-\frac1k\Bigr)^k\Bigr)\min_{i\in S}a_i\;\le\;u(S).
--   $$
--
--   This is the lower half of Lemma 4: replication scores are a $(1-1/e)$-minorant sketch of $u$ on the sets of size $k$.
--
--   Differences from the source:
--
--   - generalization: stated inside the proof of Lemma 4, where g also has extended diminishing returns → no extended diminishing returns hypothesis; reason: not used by this step; the Lean statement specializes to the source's
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication scores aᵢ = E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁾,φ,…,φ)] of (7) → the k-fold replica y ↦ g(pad y) is integrable under the k-fold product of Pᵢ, for each i; reason: what (7) presupposes; integrability of every u(S) and of t ↦ g(z, t) follows from it and is not assumed
--   - encoding: N = {1,…,n} with 0 < k ≤ n; nonnegative independent Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → items Fin (m + 1) (n = m + 1); Pᵢ probability measures on ℝ≥0, independence as Measure.pi; g : (Fin (m+1) → ℝ≥0) → ℝ with 0 ≤ g x; reason: n ≥ 1 is forced by 0 < k ≤ n; same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Appendix D, proof of the lower bound of Lemma 4, pp.35–36

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_utility
import Definitions.Def_TestScoreSubmod_repScore

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **The cascade: lower bound of Lemma 4** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Appendix
D, pp.35–36: "From this, we can use a cascading argument to show that
u(S) ≥ (1 − (1 − 1/k)ᵏ) a₁ ≥ (1 − 1/e) a₁", with `a₁ = min{aᵢ | i ∈ S}`).

Let `0 < k ≤ n = m + 1`, `g` a nonnegative, measurable, symmetric, monotone submodular value
function, `Xᵢ ∼ Pᵢ` independent with integrable `k`-fold replicas, `u` the utility (4) and
`aᵢ` the replication test scores (7). For every set `S` with `|S| = k`,

`(1 − 1/e) min_{i∈S} aᵢ ≤ (1 − (1 − 1/k)ᵏ) min_{i∈S} aᵢ ≤ u(S)`.

**Formalization Note** The minimum is `Finset.inf'`, over `S`, which is nonempty since
`|S| = k > 0`. `Measurable g` and the integrability of the replicas are what the expectations
presuppose. -/
theorem lemma_4_lower {m k : ℕ} (hk : 0 < k) (hkn : k ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (P : Fin (m + 1) → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (P i)]
    (hint : ∀ i, Integrable (fun y : Fin k → ℝ≥0 => g (pad y)) (Measure.pi fun _ : Fin k => P i))
    (S : Finset (Fin (m + 1))) (hS : S.card = k) :
    (1 - 1 / Real.exp 1) * S.inf' (Finset.card_pos.mp (hS ▸ hk)) (repScore g P k) ≤
        (1 - (1 - 1 / (k : ℝ)) ^ k) * S.inf' (Finset.card_pos.mp (hS ▸ hk)) (repScore g P k) ∧
      (1 - (1 - 1 / (k : ℝ)) ^ k) * S.inf' (Finset.card_pos.mp (hS ▸ hk)) (repScore g P k) ≤
        utility g P S := by sorry

end TestScoreSubmod
