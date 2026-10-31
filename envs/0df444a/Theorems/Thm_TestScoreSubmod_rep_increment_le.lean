-- Prove2me | Theorems.Thm_TestScoreSubmod_rep_increment_le
-- name    : TestScoreSubmod.rep_increment_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:43.954978+00:00
-- url     : https://prove2.me/theorems/6f5c6a55-3eeb-44ba-b176-6a1bc21b8357
-- title:
--   Inequality (c): the $k$-th replica adds at most $a_i/k$
-- statement:
--   Let $k=r+1\le n=m+1$, let $g:\mathbb R_+^n\to\mathbb R_+$ be a measurable, symmetric, monotone submodular value function, and let $P_i$ be a probability law on $\mathbb R_+$ under which the $k$-fold replica has integrable value. Write $a_i^{(j)}=\mathbb E[g(X_i^{(1)},\dots,X_i^{(j)},0,\dots,0)]$ for $j$ independent replicas $X_i^{(t)}\sim P_i$, so that $a_i=a_i^{(k)}$.
--   Then
--
--   $$
--   a_i^{(k)}-a_i^{(k-1)}\le\frac{a_i}{k}.
--   $$
--
--   In the paper's notation, $u(\{i^{(1)},\dots,i^{(k)}\})-u(\{i^{(1)},\dots,i^{(k-1)}\})\le a_i/k$: the last of $k$ independent replicas of an item contributes at most a $1/k$ share of their joint value. It is step (c) of the upper bound of Lemma 4.
--
--   Differences from the source:
--
--   - reading: the chain … = (1/k) Σ_j (u({i⁽¹⁾,…,i⁽ʲ⁺¹⁾}) − u({i⁽¹⁾,…,i⁽ʲ⁾})) = (1/k) u({i⁽¹⁾,…,i⁽ᵏ⁾}) = aᵢ/k → its end-to-end inequality a_i^(k) − a_i^(k−1) ≤ a_i/k; reason: the telescoping sum equals (aᵢ − g(0))/k, so the printed middle equality holds only when g(0) = 0; the end-to-end inequality holds in general
--   - encoding: u({i⁽¹⁾,…,i⁽ʲ⁾}) for j replicas of item i (footnote 6) → repScore g P j i; reason: the expectation of g at j independent replicas padded with φ = 0, as in (16), p.35
--   - generalization: stated inside the proof of Lemma 4, where g also has extended diminishing returns → no extended diminishing returns hypothesis; reason: not used by this step; the Lean statement specializes to the source's
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication score aᵢ of (7) with k = r + 1 replicas → the (r + 1)-fold replica y ↦ g(pad y) is integrable; reason: what (7) presupposes; the integrability of the other expectations follows from it
--   - encoding: k replicas, k − 1 replicas, 0 < k ≤ n; nonnegative Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → k = r + 1 with r + 1 ≤ m + 1 = n; Pᵢ a probability measure on ℝ≥0; replicas as Measure.pi over Fin r; 0 ≤ g x; reason: avoids natural-number subtraction k − 1; same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Appendix D, proof of the upper bound of Lemma 4, step (c), p.37

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_repScore

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **Inequality (c)** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Appendix D, step (c) of the
upper bound of Lemma 4, p.37: "u({i⁽¹⁾,…,i⁽ᵏ⁾}) − u({i⁽¹⁾,…,i⁽ᵏ⁻¹⁾}) ≤ … ≤ aᵢ/k").

Let `k = r + 1 ≤ n = m + 1`, `g` a nonnegative, measurable, symmetric, monotone submodular
value function, and `Pᵢ` a probability law on `ℝ₊` whose `k`-fold replica has integrable
value. The expected value gained by adding the `k`-th independent replica of item `i` to
`k − 1` replicas is at most `aᵢ/k`:

`E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁾)] − E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁻¹⁾)] ≤ aᵢ / k`, where `aᵢ = E[g(Xᵢ⁽¹⁾,…,Xᵢ⁽ᵏ⁾)]`.

**Formalization Note** `u({i⁽¹⁾,…,i⁽ʲ⁾})` is `repScore g P j i`, the expectation of `g` at `j`
replicas padded with `φ = 0`; all `k` replicas fit in the `n` coordinates. The printed chain's
third line is an equality only when `g(0) = 0`; in general the sum telescopes to
`aᵢ − g(0) ≤ aᵢ`, and the end-to-end inequality is what is stated. -/
theorem rep_increment_le {m r : ℕ} (hr : r + 1 ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (P : Fin (m + 1) → Measure ℝ≥0) (i : Fin (m + 1)) [IsProbabilityMeasure (P i)]
    (hint : Integrable (fun y : Fin (r + 1) → ℝ≥0 => g (pad y))
      (Measure.pi fun _ : Fin (r + 1) => P i)) :
    repScore g P (r + 1) i - repScore g P r i ≤ repScore g P (r + 1) i / ((r : ℝ) + 1) := by sorry

end TestScoreSubmod
