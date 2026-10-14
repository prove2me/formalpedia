-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_lemma_4_4_iii
-- name    : RankBasedSDI.LoadBalancing.lemma_4_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:31.477271+00:00
-- url     : https://prove2.me/theorems/80bf0486-addf-4ef4-a27f-380f37ef4c0a
-- title:
--   Lemma 4.4(iii): $\hat P^n$, $\hat L^n$, $\hat X^n$ are C-tight and $\hat M^n\to0$ in probability
-- statement:
--   Consider a sequence of load-balancing systems satisfying (2.9)–(2.13), and assume (IC₀). Then the following hold:
--
--   1. the sequences $\hat P^n=(\hat P^n_i)_{i\in[N]}$, $\hat L^n$ and $\hat X^n$ are C-tight;
--   2. $\hat M^n\to0$ in probability, uniformly on compact time intervals: for every $t\ge0$ and $\varepsilon>0$,
--
--   $$
--   P\Big(\sup_{s\in[0,t]}\|\hat M^n(s)\|\ge\varepsilon\Big)\to0 .
--   $$
--
--   These are the tightness ingredients of Proposition 4.1(i).
--
--   **Formalization Note** C-tightness of an $N$-dimensional sequence is equivalent to C-tightness of each coordinate, the paper's "$\hat P^n_i$, $\hat L^n_i$ and $\hat X^n_i$ are C-tight". "$\to0$ in probability" for a process is read as u.o.c. convergence in probability (the referenced `UocInProb`). This is what the proof gives (martingale inequality and the second moment) and what Proposition 4.1 uses.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 13, Lemma 4.4(iii) (standing assumption (IC₀) of §4.1, p. 11)

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

theorem lemma_4_4_iii {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) (μ₀ : ProbabilityMeasure (Fin N → ℝ))
    (hIC : IC0 S μ₀) :
    IsCTight S.P (Phat S) ∧ IsCTight S.P (Lhat S) ∧ IsCTight S.P (Xhat S) ∧
      UocInProb S.P (Mhat S) (fun _ _ => 0) := by sorry

end RankBasedSDI.LoadBalancing
