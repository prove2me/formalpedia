-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_lemma_4_4_i
-- name    : RankBasedSDI.LoadBalancing.lemma_4_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:14.20556+00:00
-- url     : https://prove2.me/theorems/c865cb32-f41a-467f-be70-1f3c100429c6
-- title:
--   Lemma 4.4(i): $\hat X^n_i=\hat U^n_i+\hat L^n_i$, $\hat L^n_i\in C^\uparrow_0$, $\int\hat X^n_i\,d\hat L^n_i=0$ and $(\hat X^n_i,\hat L^n_i)=\Gamma(\hat U^n_i)$
-- statement:
--   Consider a sequence of load-balancing systems satisfying the scaling conditions (2.9)–(2.13), in particular critical load $\lambda_i=\mu_i$. Let $n\in\mathbb N$ and $i\in[N]$. Then almost surely the following hold:
--
--   1. for all $t\ge0$,
--
--   $$
--   \hat X^n_i(t)=\hat U^n_i(t)+\hat L^n_i(t),\qquad \hat U^n_i(t)=\hat X^n_i(0-)+\hat E^n_i(t)+\hat A^n_i(t)-\hat S^n_i(T^n_i(t))+\hat m^n_it \quad(4.8);
--   $$
--
--   2. the sample path of $\hat L^n_i$ lies in $C^\uparrow_0$, and $\int_0^\infty\hat X^n_i(t)\,d\hat L^n_i(t)=0$ (4.9);
--   3. $(\hat X^n_i,\hat L^n_i)=\Gamma(\hat U^n_i)$ (4.10), i.e. $\hat L^n_i(t)=\sup_{s\le t}(\hat U^n_i)^-(s)$ and $\hat X^n_i(t)=\hat U^n_i(t)+\hat L^n_i(t)$ for $t\ge0$.
--
--   This is the pathwise reflection representation of the scaled queue length. Tightness and the identification of limits are built on it.
--
--   **Formalization Note** (IC₀), the standing assumption of §4.1, is not used. The paper notes (p. 15) that parts (i) and (ii) hold without it. The statement is a.s. because the model equations are. The integral in (4.9) is the `lintegral` complementarity of `Reflection`.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, pp. 12–13, Lemma 4.4(i), (4.8)–(4.10)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
import Definitions.Def_RankBasedSDI_LoadBalancing_Model
import Definitions.Def_RankBasedSDI_LoadBalancing_ScaledProcesses
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace RankBasedSDI.LoadBalancing

theorem lemma_4_4_i {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) (n : ℕ) (i : Fin N) :
    ∀ᵐ ω ∂S.P,
      (∀ t : ℝ, 0 ≤ t → Xhat S n ω t i = Uhat H n ω t i + Lhat S n ω t i) ∧
      IsC0Up (fun t => Lhat S n ω t i) ∧
      StieltjesComplementary (fun t => Xhat S n ω t i) (fun t => Lhat S n ω t i) ∧
      (∀ t : ℝ, 0 ≤ t →
        Xhat S n ω t i = Uhat H n ω t i + skorokhodReg (fun s => Uhat H n ω s i) t ∧
        Lhat S n ω t i = skorokhodReg (fun s => Uhat H n ω s i) t) := by sorry

end RankBasedSDI.LoadBalancing
