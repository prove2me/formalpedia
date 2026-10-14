-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_3_2
-- name    : SelfStructIS.LogEff.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:06.660464+00:00
-- url     : https://prove2.me/theorems/ba1f4a66-1018-48aa-9e2d-4a89f7547c4a
-- title:
--   Lemma 3.2, p. 11 — I is continuous, positively homogeneous, with inf_{yᵢ>c} I = c
-- statement:
--   Let $X$ satisfy Assumption 3.1 with indices $\alpha$, and let $Y=\Lambda(X)$ satisfy Assumption 3.2 with $p,\varphi$ and limiting function $I$. Then:
--
--   1. $I$ is continuous on $\mathbb R^d_+\setminus\{0\}$, $I(y)\to0$ as $y\to0$ within $\mathbb R^d_+\setminus\{0\}$, and $I(y)>0$ for every $y\in\mathbb R^d_+\setminus\{0\}$;
--   2. $I$ is positively homogeneous: $I(\lambda y)=\lambda I(y)$ for every $\lambda>0$ and $y\in\mathbb R^d_+\setminus\{0\}$;
--   3. for every $c\ge0$ and every $i$,
--   $$\inf\{I(y): y\in\mathbb R^d_+,\ y_i>c\}=c.$$
--
--   These properties make $I$ a genuine rate function with compact level sets and pin down its normalization by the standard exponential marginals.
--
--   **Formalization Note** The value $I(0)$ is not determined by (13), which only constrains $I$ at $y\ne0$; the printed "$I$ continuous, $I(0)=0$" is therefore stated as continuity off the origin with limit $0$ at the origin, and homogeneity is stated off the origin. Part 3 uses that the marginals of $Y$ are standard exponential (Lemma 3.1), which needs the continuity of $\Lambda_i$ in Assumption 3.1; that assumption is added. The infimum in part 3 is a real infimum of a nonempty set bounded below by $0$.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 11, Lemma 3.2 (proof p. 44, App. D)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_3_2 (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (p φ I : (Fin d → ℝ) → ℝ) (h32 : Assumption32 μ p φ I) :
    (ContinuousOn I {y | (∀ i, 0 ≤ y i) ∧ y ≠ 0} ∧
        Tendsto I (𝓝[{y | (∀ i, 0 ≤ y i) ∧ y ≠ 0}] 0) (𝓝 0) ∧
        ∀ y : Fin d → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 → 0 < I y) ∧
      (∀ (s : ℝ) (y : Fin d → ℝ), 0 < s → (∀ i, 0 ≤ y i) → y ≠ 0 → I (s • y) = s * I y) ∧
      (∀ (c : ℝ) (i : Fin d), 0 ≤ c →
        sInf (I '' {y : Fin d → ℝ | (∀ j, 0 ≤ y j) ∧ c < y i}) = c) := by sorry

end SelfStructIS.LogEff
