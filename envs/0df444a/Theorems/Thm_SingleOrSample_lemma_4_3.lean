-- Prove2me | Theorems.Thm_SingleOrSample_lemma_4_3
-- name    : SingleOrSample.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:36.412987+00:00
-- url     : https://prove2.me/theorems/6017541b-5706-4972-8985-2f35fe5f129a
-- title:
--   Lemma 4.3 — greedy bucketing guarantee
-- statement:
--   Suppose an agent with a monotone, normalized, submodular valuation $v$ arrives after $t<n$ special rounds, let $N=n-t$, let $R$ be the remaining set, and let $Q_1,\dots,Q_N$ be pairwise disjoint sets of goods. Put $\Pi=\sum_{h=1}^N v(Q_h\cap R)$. If the agent follows the safe strategy at target $\tau>0$, then every outcome $A$ of the round satisfies
--   $$v(A)\ge\min\Bigl\{\tau,\ \frac1{k+1}\Bigl(\frac{\Pi}{N}-k\tau\Bigr)\Bigr\},$$
--   and $v(A)\ge\tau$ if $\Pi\ge(2k+1)\tau N$.
--
--   The bound is deterministic. It is the step that converts residual value of the agent's bundles into value of the agent's allocation, whatever the coins do.
--
--   Differences from the source:
--   - encoding: the parameters k and τ = 1/ck of Algorithm 2 and Definition 7 → 0 < k and any τ > 0; reason: τ > 0 is the same as a positive real c = 1/(kτ); k = 0 is not a parameter of the algorithm, since buckets would be empty
--   - encoding: v_i(A_i) ≥ … → the bound on the whole support of the round's law; reason: the page's claim is deterministic
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 4.3, p.14

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_runLaw
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample

/-- **Lemma 4.3, greedy bucketing guarantee** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 4.3, p.14). An agent arrives after `t`
special rounds, with `N = n − t` and `t < n`; for pairwise disjoint `Q_1, …, Q_N` and
`Π = ∑_h v(Q_h ∩ R)`, every outcome of the round of an agent following the safe strategy has value at
least `min{τ, (Π/N − kτ)/(k + 1)}`, and at least `τ` if `Π ≥ (2k + 1)τN`.

**Formalization Note.** Deterministic: the bound holds on the whole support of the round's law. `0 < k`
and `0 < τ` are the page's standing parameters (`τ = 1/ck`); the bound is false at `k = 0`, and the
safe strategy is only constrained for `0 < τ`. No value of `MMS` is used, as on the page. -/
theorem lemma_4_3 {m n k : ℕ} (hk : 0 < k) {τ : ℝ} (hτ : 0 < τ) (v : Finset (Fin m) → ℝ)
    (hv : IsValuation v) (hsub : SubsamplingSM.Offline.IsSubmodular v) (σ : Strategy m)
    (hσ : IsSafe n k τ v σ) (h : Hist m) (ht : specialCount h < n)
    (Q : Fin (n - specialCount h) → Finset (Fin m)) (hQ : Pairwise (Function.onFun Disjoint Q))
    (r : Round m) (hr : r ∈ (roundLaw n k σ h).support) :
    let N : ℝ := ((n - specialCount h : ℕ) : ℝ)
    let S : ℝ := ∑ b, v (Q b ∩ remaining h)
    min τ ((1 / ((k : ℝ) + 1)) * (S / N - (k : ℝ) * τ)) ≤ v r.goods ∧
    ((2 * (k : ℝ) + 1) * τ * N ≤ S → τ ≤ v r.goods) := by sorry

end SingleOrSample
