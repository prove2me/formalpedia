-- Prove2me | Theorems.Thm_RobustKZClust_Main_fact_6_2
-- name    : RobustKZClust.Main.fact_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:11:43.882921+00:00
-- url     : https://prove2.me/theorems/6d2c5ade-3f5f-4725-b012-cb42e75ed903
-- title:
--   Fact 6.2 — opt(µ) = 0 if |supp µ| ≤ k, otherwise opt(µ) ≥ 2^{1−z}, for integer µ ≥ 0 on [∆]^d
-- statement:
--   Let $k,z\ge1$ and let $\mu$ be a frequency vector on the grid $X=[\Delta]^d$ with nonnegative integer entries. Then:
--
--   1. if $|\mathrm{supp}(\mu)|\le k$, some nonempty center set with at most $k$ points has cost $0$, and $\mathrm{opt}(\mu)=0$;
--   2. otherwise
--   $$\mathrm{opt}(\mu)\ge2^{1-z}.$$
--
--   This lower bound on nonzero clustering costs is what lets the algorithm round query centers to a grid at an additive cost that is small relative to the cost itself (Lemma 6.3).
--
--   **Formalization Note.** $\mu$ is a finitely supported real weight vector on $\mathbb R^d$ whose support lies in $[\Delta]^d$ and whose values are natural numbers. $\mathrm{opt}$ is the infimum over nonempty center sets with at most $k$ points.
--
--   Differences from the source:
--   - encoding: µ ∈ Z^X_{≥0} → a finitely supported weight vector on ℝ^d with support in [∆]^d and natural-number values; reason: the mission's common cost convention.
--   - encoding: opt(µ) = 0 with opt a minimum → opt as an infimum equals 0 and some admissible center set has cost 0; reason: the minimum is written as sInf, so its attainment is stated explicitly.
--   - reading: opt over C ⊆ R^d with |C| ≤ k → over nonempty C; reason: dist(x, ∅) is undefined.
--   - reading: the number of centers k → k ≥ 1; reason: with nonempty center sets k = 0 admits no center set at all, and (k, z)-clustering asks for at least one center.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 28, Fact 6.2

import Mathlib
import Definitions.Def_RobustKZClust_Main_Cost

namespace RobustKZClust.Main

/-- Fact 6.2 (p. 28): for an integer frequency vector `µ ≥ 0` on `X = [∆]^d`, `opt(µ) = 0`
(attained) if `|supp µ| ≤ k`, and `opt(µ) ≥ 2^{1−z}` otherwise. -/
theorem fact_6_2 (k z d Δ : ℕ) (hk : 1 ≤ k) (hz : 1 ≤ z) (μ : Pt d →₀ ℝ)
    (hX : ∀ x ∈ μ.support, x ∈ grid d Δ) (hN : ∀ x, ∃ n : ℕ, μ x = n) :
    (μ.support.card ≤ k →
      opt k z μ = 0 ∧ ∃ C : Finset (Pt d), Admissible k C ∧ cost z μ C = 0) ∧
    (k < μ.support.card → (2 : ℝ) ^ ((1 : ℤ) - z) ≤ opt k z μ) := by sorry

end RobustKZClust.Main
