-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_8
-- name    : RobustSAA.Discrete.Supplement.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:43:14.066727+00:00
-- url     : https://prove2.me/theorems/f9c3fdd6-dd61-4833-8d63-deeb7f59aa4f
-- title:
--   Theorem 8 (corrected: positive threshold; G-test minimum attained when all p̂(j) > 0) — χ² and G-test worst cases as SOC and exponential-cone programs
-- statement:
--   Let $\Xi=\{\hat\xi^1,\dots,\hat\xi^n\}$ be a known finite support, $N\ge1$, data $\xi^1,\dots,\xi^N$ with empirical frequencies $\hat p_N(j)$, and $q>0$ the threshold. Let $\mathcal F^\alpha_{X_N}=\{F_0: X_N(F_0)\le q\}$ and $\mathcal F^\alpha_{G_N}=\{F_0: G_N(F_0)\le q\}$ be the regions of Pearson's $\chi^2$ test and of the G-test (the published regions with parameter $Nq^2$, i.e. radius $\sqrt{Nq^2/N}=q$). Assume the hypotheses of Theorem 1: $X$ closed, $C(x_0;\mathcal F)<\infty$ for some $x_0\in X$, the costs $c(\cdot;\hat\xi^j)$ equicontinuous, and $X$ compact or $c(x;\hat\xi^j)\to\infty$ as $\|x\|\to\infty$. Then for every $x\in X$:
--
--   1. $C(x;\mathcal F^\alpha_{X_N})$ equals the minimum, attained, of
--   $$r+q^2s-\sum_j\hat p_N(j)t_j\ \text{ s.t. } s\ge0,\ y\ge0,\ s+r\ge c_j,\ 2s+t_j\le y_j,\ (2s-c_j+r,\,r-c_j,\,y_j)\in C^3_{SOC},\ c_j\ge c(x;\hat\xi^j).$$
--   2. $C(x;\mathcal F^\alpha_{G_N})$ equals the infimum of
--   $$r+\tfrac12q^2s-\sum_j\hat p_N(j)t_j\ \text{ s.t. } s\ge0,\ (t_j,s,s+r-c_j)\in C_{XC},\ c_j\ge c(x;\hat\xi^j),$$
--   and this infimum is attained whenever $\hat p_N(j)>0$ for every $j$.
--
--   These single-level programs turn the robust problem over a finite support into a conic program in $(x,r,s,t,\dots)$.
--
--   Differences from the source:
--   - encoding: thresholds Q_{X_N}(α), Q_{G_N}(α) and the regions F^α_{X_N}, F^α_{G_N} → a real q and the published chiRegion/gRegion with parameter N·q², whose radius √(Nq²/N) is q for N ≥ 1; reason: the published regions take the squared-radius parameter Q with radius √(Q/N)
--   - correction: the χ² and G minima for every threshold Q(α) → q > 0; reason: at q = 0 the region is {p̂} and the χ² program's infimum is not attained when costs differ on the observed support (DISPROOF.md: n = 2, p̂ = (½,½), c = (0,1)); the source's thresholds are positive quantiles; excluded: q = 0
--   - correction: C(x; F^α_{G_N}) = min of (27) → C(x; F^α_{G_N}) = inf of (27), attained when every p̂_N(j) > 0; reason: DISPROOF.md: n = 2, p̂ = (1, 0), costs (0, 1): C = 1 − e^{−q²/2}, but the unique dual optimum needs c₂ = r + s with s > 0, where (t₂, s, 0) ∉ C_XC; no restriction of the equality itself
--   - encoding: support points ξ̂¹, …, ξ̂ⁿ → labels Fin n with points ξ̂ : Fin n → ℝ^d and costs c(x; ξ̂ʲ); reason: the published discrete setting uses labels; distinctness of the points plays no role
--   - encoding: min → IsMinValue: the extended-real infimum, attained when the program is feasible; reason: same instances
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 8, p. 16 (proof §10.12, pp. 40–41)

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_DiscreteDual

namespace RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Discrete

theorem theorem_8 {n N d dx : ℕ} (hN : 0 < N) (smp : Fin N → Fin n)
    (ξhat : Fin n → RobustSAA.Convergence.Pt d) (X : Set (RobustSAA.Convergence.Pt dx))
    (hX : IsClosed X) (c : RobustSAA.Convergence.Pt dx → RobustSAA.Convergence.Pt d → ℝ)
    (hequi : Equicontinuous (fun j : Fin n => fun x => c x (ξhat j)))
    (hcomp : IsCompact X ∨
      ∀ j, Tendsto (fun x => c x (ξhat j))
        (Bornology.cobounded (RobustSAA.Convergence.Pt dx)) atTop)
    (x : RobustSAA.Convergence.Pt dx) (hx : x ∈ X) (q : ℝ) (hq : 0 < q) :
    ((∃ x₀ ∈ X, discWorstCase (chiRegion ((N : ℝ) * q ^ 2) N smp)
        (fun j => c x₀ (ξhat j)) < ⊤) →
      IsMinValue (discWorstCase (chiRegion ((N : ℝ) * q ^ 2) N smp) (fun j => c x (ξhat j)))
        (chiDualValues q smp (fun j => c x (ξhat j)))) ∧
    ((∃ x₀ ∈ X, discWorstCase (gRegion ((N : ℝ) * q ^ 2) N smp)
        (fun j => c x₀ (ξhat j)) < ⊤) →
      discWorstCase (gRegion ((N : ℝ) * q ^ 2) N smp) (fun j => c x (ξhat j)) =
          sInf ((fun v : ℝ => (v : EReal)) '' gDualValues q smp (fun j => c x (ξhat j))) ∧
        ((∀ j, 0 < phat smp j) →
          IsMinValue (discWorstCase (gRegion ((N : ℝ) * q ^ 2) N smp)
            (fun j => c x (ξhat j))) (gDualValues q smp (fun j => c x (ξhat j))))) := by sorry

end RobustSAA.Discrete.Supplement
