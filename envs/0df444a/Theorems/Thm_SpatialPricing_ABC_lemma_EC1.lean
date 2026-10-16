-- Prove2me | Theorems.Thm_SpatialPricing_ABC_lemma_EC1
-- name    : SpatialPricing.ABC.lemma_EC1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:38.74507+00:00
-- url     : https://prove2.me/theorems/dd9e6328-8432-4a7a-bd94-575a5bef5c89
-- title:
--   Lemma EC.1, ec2 — maximal deviation bound for independent Bernoulli demands
-- statement:
--   Fix a deterministic schedule of demand rates $\lambda_{t,ij}\in[0,1]$, an arc $i\to j$, periods $1\le t_1<t_2\le T$, a threshold $y\ge0$, and $q\in(0,1]$. Let $D_{s,ij}$ be independent Bernoulli demands with these rates and $\delta_{s,ij}=D_{s,ij}-\lambda_{s,ij}$. Then
--
--   $$\Pr\!\left(\max_{t_1\le t\le t_2}\left|\sum_{s=t_1}^t\delta_{s,ij}\right|>y\right)\le2\exp\!\left(\sum_{s=t_1}^{t_2}\min\{\lambda_{s,ij},1-\lambda_{s,ij}\}q^2-qy\right)\le2\exp\!\left((t_2-t_1)q^2-qy\right).$$
--
--   The two bounds control the maximum cumulative fluctuation along one arc over a consecutive interval.
--
--   **Formalization Note** The statement takes deterministic rates, for which the right side of (EC.1) is a number. The paper later applies the bound to adaptive ABC rates; that use requires a separate martingale argument. No standing revenue assumptions are needed here.
-- source:
--   Chen, Lei, Jasin, accepted manuscript, LBS Research Online eprint 2845, PDF sha256 7310a8a1…480a, p. ec2, Lemma EC.1, (EC.1)–(EC.2) (PDF 43)

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting

namespace SpatialPricing.ABC

/-- Lemma EC.1, ec2, in its deterministic-rate reading. -/
theorem lemma_EC1 (P : Instance)
    (x : ℕ → Fin P.N → Fin P.N → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 P.T, ∀ i j, 0 ≤ x t i j ∧ x t i j ≤ 1)
    (t1 t2 : ℕ) (ht1 : 1 ≤ t1) (ht12 : t1 < t2) (ht2 : t2 ≤ P.T)
    (i j : Fin P.N) (y q : ℝ) (hy : 0 ≤ y) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    let π : ℕ → P.Path → Fin P.N → Fin P.N → ℝ := fun t _ i j => x t i j
    let S : P.Path → Prop := fun ω =>
      ∃ t ∈ Finset.Icc t1 t2,
        y < |∑ s ∈ Finset.Icc t1 t, (P.D s ω i j - x s i j)|
    P.prob π S ≤
      2 * Real.exp ((∑ s ∈ Finset.Icc t1 t2,
        min (x s i j) (1 - x s i j)) * q ^ 2 - q * y) ∧
    2 * Real.exp ((∑ s ∈ Finset.Icc t1 t2,
      min (x s i j) (1 - x s i j)) * q ^ 2 - q * y) ≤
        2 * Real.exp (((t2 - t1 : ℕ) : ℝ) * q ^ 2 - q * y) := by sorry

end SpatialPricing.ABC
