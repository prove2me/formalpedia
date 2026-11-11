-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_theorem_10_1
-- name    : PriceCapacities.LowerBound.theorem_10_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:24:28.875317+00:00
-- url     : https://prove2.me/theorems/ff04e098-ca18-4c3e-8d95-5e6f5e976913
-- title:
--   Theorem 10.1 — every capacitated ε-coreset has size Ω̃_z(kε⁻² min{k^{z/2}, ε⁻ᶻ}) for z ∈ {1,2} and Ω̃_z(kε⁻ᶻ min{k, ε⁻²}) for z > 2
-- statement:
--   Fix an integer $z\ge1$. There are $c>0$ and $L\in\mathbb N$, depending only on $z$, such that for every integer $k\ge2$ and every $0<\varepsilon<1/4$ there is an unweighted set $P$ of $n\ge k/\varepsilon$ distinct points in a Euclidean space $\mathbb R^{\dim}$ (the dimension is unrestricted) such that every capacitated $\varepsilon$-coreset $Q$ for $P$ — any weighted point set in $\mathbb R^{\dim}$ with nonnegative weights and total weight $n$ satisfying $|\mathrm{cost}_Q(C,h)-\mathrm{cost}_P(C,h)|\le\varepsilon\,\mathrm{cost}_P(C,h)$ for all center tuples $C\in(\mathbb R^{\dim})^k$ and all loads $h\ge0$ with $\sum_ih_i=n$ — has size
--   $$|\operatorname{supp}Q|\ \ge\ \begin{cases}c\,\dfrac{k\varepsilon^{-2}\min\{k^{z/2},\varepsilon^{-z}\}}{\log(ek/\varepsilon)^L}, & z\in\{1,2\},\\[2ex] c\,\dfrac{k\varepsilon^{-z}\min\{k,\varepsilon^{-2}\}}{\log(ek/\varepsilon)^L}, & z>2.\end{cases}$$
--   That is, every capacitated coreset has size $\tilde\Omega_z(k\varepsilon^{-2}\min\{k^{z/2},\varepsilon^{-z}\})$ for $z\in\{1,2\}$ and $\tilde\Omega_z(k\varepsilon^{-z}\min\{k,\varepsilon^{-2}\})$ for $z>2$. Together with the matching upper bounds of the paper this separates capacitated from unconstrained coresets: for $k$-median $\tilde\Theta(k^{3/2}\varepsilon^{-2})$ versus $\tilde\Theta(k^{4/3}\varepsilon^{-2})$, and for $k$-means $\tilde\Theta(k^2\varepsilon^{-2})$ versus $\tilde\Theta(k^{3/2}\varepsilon^{-2})$, when $k\le\varepsilon^{-2}$.
--
--   Differences from the source:
--
--   - encoding: Ω̃_z(B): constants depending only on z and polynomial factors in log(ek/ε) suppressed → c·B / log(ek/ε)^L with c > 0 and L ∈ ℕ depending only on z, quantified before k and ε; reason: the convention stated on p. 32; log(ek/ε) ≥ 1 on the domain
--   - encoding: an unweighted set P of n distinct Euclidean points; the dimension is unrestricted → ∃ dim, a Finset P of EuclideanSpace ℝ (Fin dim), each point with weight one, n = |P|; reason: a Finset has distinct elements; the weighted set is `unweighted P`
--   - encoding: the size of Q is the number of distinct points with positive weight; Q any weighted point set in ℝ^d → size Q = |supp Q| for Q : EuclideanSpace ℝ (Fin dim) →₀ ℝ≥0; reason: Definition 2.2 and §2.2 (finitely supported nonnegative weights)
--   - encoding: cost_P(C, h) is the minimum of the assignment LP → capCost = sInf of the costs of the feasible fractional assignments; reason: for h ∈ H the feasible set is nonempty and the minimum is attained; all costs are ≥ 0
--   - encoding: center tuples C ∈ (ℝ^d)^k, loads h ∈ ℝ^k_{≥0} with Σh_i = n, indices 1..k → C : Fin k → ℝ^d (repetitions allowed), h : Fin k → ℝ with h ≥ 0 and Σh = 1(P), 0-based; reason: same objects; Lean index base
--   - encoding: the two cases z ∈ {1, 2} and z > 2; k^{z/2}, ε^{−2}, ε^{−z} → if z = 1 ∨ z = 2 then … else … (z : ℕ, 1 ≤ z); (k : ℝ)^((z : ℝ)/2), (ε²)⁻¹, (εᶻ)⁻¹; reason: same cases and values
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 32, Theorem 10.1

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset

namespace PriceCapacities.LowerBound

theorem theorem_10_1 (z : ℕ) (hz : 1 ≤ z) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ,
      ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∃ (dim : ℕ) (P : Finset (EuclideanSpace ℝ (Fin dim))),
          (k : ℝ) / ε ≤ (P.card : ℝ) ∧
          ∀ Q : WeightedSet (EuclideanSpace ℝ (Fin dim)),
            IsCapacitatedCoreset k (z : ℝ) ε (unweighted P) Q →
              (if z = 1 ∨ z = 2 then
                  c * k * (ε ^ 2)⁻¹ * min ((k : ℝ) ^ ((z : ℝ) / 2)) ((ε ^ z)⁻¹)
                    / Real.log (Real.exp 1 * k / ε) ^ L
                else
                  c * k * (ε ^ z)⁻¹ * min (k : ℝ) ((ε ^ 2)⁻¹)
                    / Real.log (Real.exp 1 * k / ε) ^ L) ≤ (size Q : ℝ) := by sorry

end PriceCapacities.LowerBound
