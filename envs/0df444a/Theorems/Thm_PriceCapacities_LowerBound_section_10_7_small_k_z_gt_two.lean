-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_section_10_7_small_k_z_gt_two
-- name    : PriceCapacities.LowerBound.section_10_7_small_k_z_gt_two
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:16.851898+00:00
-- url     : https://prove2.me/theorems/2e919637-fd25-4569-ac41-61c2b89d10a6
-- title:
--   §10.7, $k=2,3$ and integer $z>2$ — every capacitated $\varepsilon$-coreset has size $\tilde\Omega_z(\varepsilon^{-z})$
-- statement:
--   Let $z>2$ be an integer. There are $c>0$ and $L\in\mathbb N$ such that for $k\in\{2,3\}$ and every $0<\varepsilon<1/4$ there is an unweighted set $P$ of $n\ge k/\varepsilon$ distinct points in some $\mathbb R^{\dim}$ such that every capacitated $\varepsilon$-coreset $Q$ for $P$ ($k$ centers, exponent $z$) has
--   $$|\operatorname{supp}Q|\ \ge\ c\,\frac{\varepsilon^{-z}}{\log(ek/\varepsilon)^L},$$
--   i.e. size $\tilde\Omega_z(\varepsilon^{-z})$. The construction uses queries with at most two centers (padded to $k$ with zero-load centers) on $A=2^D$ separated vertex groups. For $k\le3$ and $\varepsilon<1/4$ this is the $z>2$ branch of Theorem 10.1, since $k\varepsilon^{-z}\min\{k,\varepsilon^{-2}\}=k^2\varepsilon^{-z}$.
--
--   Differences from the source:
--
--   - reading: 'the claimed bound' for k = 2, 3 → Theorem 10.1's conclusion for k ∈ {2, 3}: an unweighted set P of n ≥ k/ε distinct points in some ℝ^dim such that every capacitated ε-coreset has the stated size; reason: the paragraph proves the k = 2, 3 case of Theorem 10.1 (p. 34, proof of Theorem 10.1)
--   - encoding: Ω̃_z(B): constants depending only on z and polynomial factors in log(ek/ε) suppressed → c·B / log(ek/ε)^L with c > 0 and L ∈ ℕ depending only on z, quantified before k and ε; reason: the convention stated on p. 32; log(ek/ε) ≥ 1 on the domain
--   - encoding: an unweighted set P of n distinct Euclidean points; the dimension is unrestricted → ∃ dim, a Finset P of EuclideanSpace ℝ (Fin dim), each point with weight one, n = |P|; reason: a Finset has distinct elements; the weighted set is `unweighted P`
--   - encoding: the size of Q is the number of distinct points with positive weight; Q any weighted point set in ℝ^d → size Q = |supp Q| for Q : EuclideanSpace ℝ (Fin dim) →₀ ℝ≥0; reason: Definition 2.2 and §2.2 (finitely supported nonnegative weights)
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), pp. 40–41, §10.7 (k = 2, 3; integer z > 2)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset

namespace PriceCapacities.LowerBound

theorem section_10_7_small_k_z_gt_two (z : ℕ) (hz : 2 < z) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ,
      ∀ k : ℕ, (k = 2 ∨ k = 3) → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∃ (dim : ℕ) (P : Finset (EuclideanSpace ℝ (Fin dim))),
          (k : ℝ) / ε ≤ (P.card : ℝ) ∧
          ∀ Q : WeightedSet (EuclideanSpace ℝ (Fin dim)),
            IsCapacitatedCoreset k (z : ℝ) ε (unweighted P) Q →
              c * (ε ^ z)⁻¹ / Real.log (Real.exp 1 * k / ε) ^ L ≤ (size Q : ℝ) := by sorry

end PriceCapacities.LowerBound
