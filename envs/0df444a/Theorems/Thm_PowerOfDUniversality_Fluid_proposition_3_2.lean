-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_proposition_3_2
-- name    : PowerOfDUniversality.Fluid.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:28.790993+00:00
-- url     : https://prove2.me/theorems/98630c7d-c4a2-4e1a-be65-1249f6f78f0b
-- title:
--   Proposition 3.2 — tail sums plus overflow are stochastically ordered, JSQ ⩽_st CJSQ(n) ⩽_st MJSQ(n)
-- statement:
--   Fix $N\ge 1$ servers, a buffer $b\ge 1$, an arrival rate $\lambda\ge 0$, an integer $n$ with $n+1\le N$, and any scheme $\Pi$ of the class CJSQ($n$). Consider three systems, run respectively under JSQ, under $\Pi$ and under MJSQ($n$), started from deterministic occupancy vectors $\mathbf Q^{JSQ}(0)$, $\mathbf Q^{CJSQ}(0)$, $\mathbf Q^{MJSQ}(0)$ with no discarded tasks. For every fixed $m\ge 1$:
--   1. if $\sum_{i\ge m'}Q^{JSQ}_i(0)\le\sum_{i\ge m'}Q^{CJSQ}_i(0)$ for every $m'\ge 1$, then
--   $$\Big\{\sum_{i=m}^{b}Q^{JSQ}_i(t)+L^{JSQ}(t)\Big\}_{t\ge0}\le_{st}\Big\{\sum_{i=m}^{b}Q^{CJSQ}_i(t)+L^{CJSQ}(t)\Big\}_{t\ge0};$$
--   2. if $\sum_{i\ge m'}Q^{CJSQ}_i(0)\le\sum_{i\ge m'}Q^{MJSQ}_i(0)$ for every $m'\ge 1$, then
--   $$\Big\{\sum_{i=m}^{b}Q^{CJSQ}_i(t)+L^{CJSQ}(t)\Big\}_{t\ge0}\le_{st}\Big\{\sum_{i=m}^{b}Q^{MJSQ}_i(t)+L^{MJSQ}(t)\Big\}_{t\ge0}.$$
--
--   Here $X\le_{st}Y$ means that there is a coupling $(X',Y')$ with the laws of $X$ and $Y$ such that almost surely $X'(t)\le Y'(t)$ for all $t\ge 0$. The comparison sandwiches every CJSQ($n$) scheme between JSQ and MJSQ($n$) at the level of tail sums.
--
--   **Formalization Note** "Provided the inequalities hold at time $t=0$" is the ordering of the initial states at every level, which is what the proof (via Proposition 3.1) needs. The three systems may live on different probability spaces; the CJSQ rule may depend on the event index, the current state and the current mark, measurably in the mark.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 12–13, Proposition 3.2

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Proposition 3.2** (p. 13, stochastic ordering JSQ ⩽_st CJSQ ⩽_st MJSQ). Fix `N ≥ 1`
servers, buffer `b ≥ 1`, arrival rate `λ ≥ 0`, `n` with `n + 1 ≤ N`, and a scheme `Π` of the
class CJSQ(n). Three systems, under JSQ, `Π` and MJSQ(n), possibly on different probability
spaces, start from deterministic occupancy vectors `QJ`, `QC`, `QM` (no discarded tasks). For
every fixed `m ≥ 1`:

1. if `∑_{i≥m'} QJ_i ≤ ∑_{i≥m'} QC_i` for every `m' ≥ 1`, then
   `{∑_{i=m}^{b} Q^{JSQ}_i(t) + L^{JSQ}(t)}_{t≥0} ⩽_st {∑_{i=m}^{b} Q^{CJSQ}_i(t) + L^{CJSQ}(t)}_{t≥0}`;
2. if `∑_{i≥m'} QC_i ≤ ∑_{i≥m'} QM_i` for every `m' ≥ 1`, then
   `{∑_{i=m}^{b} Q^{CJSQ}_i(t) + L^{CJSQ}(t)}_{t≥0} ⩽_st {∑_{i=m}^{b} Q^{MJSQ}_i(t) + L^{MJSQ}(t)}_{t≥0}`. -/
theorem proposition_3_2 (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (n : ℕ) (hn : n + 1 ≤ N) (pol : Scheme) (hpol : IsCJSQ n pol)
    {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (P₃ : Measure Ω₃)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure P₃]
    (sysJ : System P₁ N b lam) (sysC : System P₂ N b lam) (sysM : System P₃ N b lam)
    (QJ QC QM : ℕ →₀ ℕ) (hJ : ∀ ω, sysJ.Q0 ω = QJ) (hC : ∀ ω, sysC.Q0 ω = QC)
    (hM : ∀ ω, sysM.Q0 ω = QM) (m : ℕ) (hm : 1 ≤ m) :
    ((∀ m' : ℕ, 1 ≤ m' → tailSum QJ m' ≤ tailSum QC m') →
      ProcLeSt P₁ P₂
        (fun ω t => ((tailSum (sysJ.occ jsq ω t) m + sysJ.overflow jsq ω t : ℕ) : ℝ))
        (fun ω t => ((tailSum (sysC.occ pol ω t) m + sysC.overflow pol ω t : ℕ) : ℝ))) ∧
    ((∀ m' : ℕ, 1 ≤ m' → tailSum QC m' ≤ tailSum QM m') →
      ProcLeSt P₂ P₃
        (fun ω t => ((tailSum (sysC.occ pol ω t) m + sysC.overflow pol ω t : ℕ) : ℝ))
        (fun ω t => ((tailSum (sysM.occ (mjsq n) ω t) m + sysM.overflow (mjsq n) ω t : ℕ) : ℝ))) := by sorry

end PowerOfDUniversality.Fluid
