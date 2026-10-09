-- Prove2me | Theorems.Thm_SBMThreshold_Main_lemma_4_7
-- name    : SBMThreshold.Main.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:29.219538+00:00
-- url     : https://prove2.me/theorems/6588bb5c-d84e-4764-a4e4-b9587d6bf125
-- title:
--   Lemma 4.7, p. 19 — at most k^{5k_r+4k_r k/ℓ+8k_r t} n^{k_n−1} non-backtracking paths u → v with t ℓ-tangles
-- statement:
--   Let $n,k,\ell,t,k_n,k_r$ be natural numbers with $k_r\ge1$ and $\ell\ge1$, and let $u\ne v$ be vertices of $\{1,\dots,n\}$. The number of non-backtracking paths $\gamma$ of length $k$ from $u$ to $v$ (in the complete graph) that have exactly $t$ $\ell$-tangles and satisfy $k_n(\gamma)=k_n$, $k_r(\gamma)=k_r$ is at most
--   $$
--   k^{\,5k_r+4k_rk/\ell+8k_rt}\;n^{\,k_n-1}.
--   $$
--
--   When $k=O(\log n)$, $k_r=O(1)$ and $\ell=\omega(\log\log n)$ the bound is $k^{O(t)}n^{k_n-1+o(1)}$: every new step but the last one has about $n$ choices, and the rest of the path costs only a sub-polynomial factor unless it has many tangles. This is the count behind the second-moment and tangle estimates of §§5–6.
--
--   **Formalization Note** The paths are non-backtracking and of length $k$, as fixed in §4 before Definition 4.6 ("they need to be non-backtracking and without many tangles"; the proof uses non-backtracking). The endpoints are distinct: the proof's factor $n^{k_n-1}$ uses that the final vertex is first reached by a new step, which fails for $u=v$, and every use of the lemma has $u\ne v$. $\ell\ge1$ makes $k/\ell$ meaningful; the exponents are real numbers.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 19, Lemma 4.7 (with the standing conventions of §4, pp. 17–18)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

open scoped Classical in
/-- Lemma 4.7 (p. 19): if `k_r ≥ 1`, there are at most `k^{5k_r + 4k_r k/ℓ + 8k_r t} n^{k_n - 1}`
non-backtracking paths of length `k` from `u` to `v ≠ u` with `t` ℓ-tangles, `k_n(γ) = k_n` and
`k_r(γ) = k_r`. -/
theorem lemma_4_7 (n k ℓ t kn kr : ℕ) (hkr : 1 ≤ kr) (hℓ : 1 ≤ ℓ) (u v : Fin n) (huv : u ≠ v) :
    ((univ.filter (fun γ : Fin (k + 1) → Fin n =>
        IsNonBacktracking γ ∧ γ 0 = u ∧ γ (Fin.last k) = v ∧ tangleCount ℓ γ = t ∧
          kNew γ = kn ∧ kRet γ = kr)).card : ℝ) ≤
      (k : ℝ) ^ ((5 * kr : ℝ) + 4 * kr * k / ℓ + 8 * kr * t) * (n : ℝ) ^ ((kn : ℝ) - 1) := by sorry

end SBMThreshold.Main
