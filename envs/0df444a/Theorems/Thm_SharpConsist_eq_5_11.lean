-- Prove2me | Theorems.Thm_SharpConsist_eq_5_11
-- name    : SharpConsist.eq_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:33.851203+00:00
-- url     : https://prove2.me/theorems/fabc1547-f625-464d-b953-11fa124f90d2
-- title:
--   Eq. (5.11) — Hoeffding without replacement for the imbalance
-- statement:
--   Fix integers $m\ge32$, $k\ge1$, $n=(m+1)k$ and $\delta=1/(64m)$. Let $A$ be a uniformly random $k$-subset of $X=[n]$. For every fixed $S\subseteq X$, of any size,
--   $$\Pr_A\bigl\{|u_A(S)|>\delta\bigr\}\le2\exp\Bigl(-\frac{2m^2\delta^2}{(m+1)^2}\,k\Bigr)\le2e^{-\delta^2k/2}.$$
--   Here $|A\cap S|$ is hypergeometric and $u_A(S)=\frac{m+1}m\bigl(\frac{|A\cap S|}k-\frac{\mathbb E|A\cap S|}k\bigr)$, so the bound is Hoeffding's inequality for sampling without replacement. It holds for queries larger than $k$ as well.
--
--   Differences from the source:
--   - encoding: probability over a uniformly random k-subset A of X → number of k-subsets A of Fin n with the property, compared with the bound times C(n, k); reason: the uniform probability of an event is its count divided by C(n, k)
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Eq. (5.11), p.16; proved in Appendix B.4, p.37

import Mathlib
import Definitions.Def_SharpConsist_uA
import Definitions.Def_SharpConsist_Fdelta

namespace SharpConsist

/-- **Eq. (5.11): Hoeffding's inequality without replacement for the imbalance.** Fu–Zhang–Tao,
*A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256
874ec76c…), §5.2, Eq. (5.11), p.16, proved in Appendix B.4, p.37. Fix integers `m ≥ 32`, `k ≥ 1`,
`n = (m+1)k`, and `δ = 1/(64m)`. For every fixed `S ⊆ X` (of any size), if `A` is a uniformly random
`k`-subset of `X`, then
`P{|u_A(S)| > δ} ≤ 2 exp(−2m²δ²k/(m+1)²) ≤ 2e^{−δ²k/2}`.

**Formalization Note.** The probability over the uniform `k`-subset `A` is written as a count: the
number of `k`-subsets `A` of `Fin n` with `|u_A(S)| > δ` is at most the bound times `C(n, k)`. -/
theorem eq_5_11 (m k n : ℕ) (hm : 32 ≤ m) (hk : 1 ≤ k) (hn : n = (m + 1) * k)
    (S : Finset (Fin n)) :
    (((Finset.univ.powersetCard k).filter (fun A : Finset (Fin n) => deltaM m < |uA k m A S|)).card : ℝ) ≤
      2 * Real.exp (-(2 * (m : ℝ) ^ 2 * deltaM m ^ 2 / ((m : ℝ) + 1) ^ 2 * (k : ℝ))) *
        (n.choose k : ℝ) ∧
    2 * Real.exp (-(2 * (m : ℝ) ^ 2 * deltaM m ^ 2 / ((m : ℝ) + 1) ^ 2 * (k : ℝ))) ≤
      2 * Real.exp (-(deltaM m ^ 2 * (k : ℝ) / 2)) := by sorry

end SharpConsist
