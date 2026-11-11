-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_lemma_10_4
-- name    : PriceCapacities.LowerBound.lemma_10_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:07.081564+00:00
-- url     : https://prove2.me/theorems/c712385b-40e5-42f1-b92d-fd61d8dfaada
-- title:
--   Lemma 10.4 — counting: for $k\ge4$ and admissible $t$, every capacitated coreset has size $\tilde\Omega_z(k\varepsilon^{-2}\min\{k,t^2\}t^{z-2})$
-- statement:
--   Fix an integer $z\ge1$. There are $\kappa_t>0$, $c>0$ and $L\in\mathbb N$, depending only on $z$, such that for every integer $k\ge4$, every $0<\varepsilon<1/4$ and every separation parameter $t\ge2$ with $\varepsilon t\Lambda^{z+20}\le\kappa_t$, where $\Lambda=\log(ek/\varepsilon)$, there is an unweighted set $P$ of $n\ge k/\varepsilon$ distinct points in some $\mathbb R^{\dim}$ such that every capacitated $\varepsilon$-coreset $Q$ for $P$ ($k$ centers, exponent $z$) has size
--   $$|\operatorname{supp}Q|\ \ge\ c\,\frac{k\,\varepsilon^{-2}\min\{k,t^2\}\,t^{z-2}}{\Lambda^L},$$
--   i.e. size $\tilde\Omega_z(k\varepsilon^{-2}\min\{k,t^2\}t^{z-2})$. Theorem 10.1 for $k\ge4$ follows by choosing $t$ within a polylogarithmic factor of $\min\{\sqrt k,\varepsilon^{-1}\}$ ($z\in\{1,2\}$) or $\varepsilon^{-1}$ ($z>2$).
--
--   Differences from the source:
--
--   - encoding: Ω̃_z(B): constants depending only on z and polynomial factors in log(ek/ε) suppressed → c·B / log(ek/ε)^L with c > 0 and L ∈ ℕ depending only on z, quantified before k and ε; reason: the convention stated on p. 32; log(ek/ε) ≥ 1 on the domain
--   - reading: t ≥ 2 'satisfying the parameter conditions in Section 10.3' → 2 ≤ t and εtΛ^{z+20} ≤ κ_t, with κ_t > 0 existentially quantified and depending only on z; reason: εtH ≤ κ_t (H = Λ^{z+20}) is the only condition §10.3 places on t; κ_t is one of its constants
--   - reading: ε (range implicit) → 0 < ε < 1/4; reason: the range of Theorem 10.1, which the lemma serves
--   - reading: second sentence: for k = 2, 3 the unconstrained bound (z ∈ {1, 2}) and §10.7 (z > 2) give the result → not part of this item; stated as the milestones section_10_7_small_k_z_one_two and section_10_7_small_k_z_gt_two; reason: it is a pointer to §10.7, whose two cases are separate items of this mission
--   - encoding: an unweighted set P of n distinct Euclidean points; the dimension is unrestricted → ∃ dim, a Finset P of EuclideanSpace ℝ (Fin dim), each point with weight one, n = |P|; reason: a Finset has distinct elements; the weighted set is `unweighted P`
--   - encoding: the size of Q is the number of distinct points with positive weight; Q any weighted point set in ℝ^d → size Q = |supp Q| for Q : EuclideanSpace ℝ (Fin dim) →₀ ℝ≥0; reason: Definition 2.2 and §2.2 (finitely supported nonnegative weights)
--   - encoding: t^{z−2} → real power t^((z : ℝ) − 2); reason: t ≥ 2 > 0; covers z = 1
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 34, Lemma 10.4

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset

namespace PriceCapacities.LowerBound

theorem lemma_10_4 (z : ℕ) (hz : 1 ≤ z) :
    ∃ κt : ℝ, 0 < κt ∧ ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ,
      ∀ k : ℕ, 4 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ t : ℝ, 2 ≤ t →
        ε * t * Real.log (Real.exp 1 * k / ε) ^ (z + 20) ≤ κt →
        ∃ (dim : ℕ) (P : Finset (EuclideanSpace ℝ (Fin dim))),
          (k : ℝ) / ε ≤ (P.card : ℝ) ∧
          ∀ Q : WeightedSet (EuclideanSpace ℝ (Fin dim)),
            IsCapacitatedCoreset k (z : ℝ) ε (unweighted P) Q →
              c * k * (ε ^ 2)⁻¹ * min (k : ℝ) (t ^ 2) * t ^ ((z : ℝ) - 2)
                  / Real.log (Real.exp 1 * k / ε) ^ L ≤ (size Q : ℝ) := by sorry

end PriceCapacities.LowerBound
