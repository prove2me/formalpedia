-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_lemma_4_3
-- name    : RankBasedSDI.LoadBalancing.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:13.516239+00:00
-- url     : https://prove2.me/theorems/43f1acc8-39e2-4fff-9937-a7c24697fe55
-- title:
--   Lemma 4.3: $\hat M^n_i$ is an $\{\mathcal F^n_t\}$-martingale with $[\hat M^n_i](t)=n^{-1}A^n_i(t)$
-- statement:
--   Consider the $n$-th load-balancing system and a server $i\in[N]$. Let $\hat M^n_i=\hat A^n_i-\hat P^n_i$ be the difference between the scaled routed LBS arrivals and their compensator $\hat P^n_i(t)=\hat\lambda^n_0\int_0^tp_{\mathcal R^n_i(s)}ds$ (4.6). Then:
--
--   1. $\hat M^n_i$ is a martingale with respect to the history filtration $\mathcal F^n_t=\sigma\{\mathcal I^n,\mathcal S^n(s),s\in[0,t]\}$, with $\hat M^n_i(t)$ integrable for every $t$;
--   2. its optional quadratic variation is
--
--   $$
--   [\hat M^n_i](t)=\sum_{s\in(0,t]}\big(\Delta\hat M^n_i(s)\big)^2=n^{-1}A^n_i(t),\qquad t\ge0,\ \text{a.s.}
--   $$
--
--   The lemma supplies the martingale part of the decomposition $\hat A^n_i=\hat P^n_i+\hat M^n_i$, and its quadratic variation gives $\hat M^n_i\to0$ in Lemma 4.4(iii).
--
--   **Formalization Note** The filtration is asserted to exist with $\mathcal F^n_t$ equal to `historySigma S n t`; this includes that these σ-algebras are increasing sub-σ-algebras. Mathlib's `Martingale` does not include integrability, so integrability is a separate conjunct. $\hat M^n_i$ is of finite variation, so its optional quadratic variation is rendered as the sum of its squared jumps over $(0,t]$, in $[0,\infty]$ (Jacod–Shiryaev I.4.52).
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 11, Lemma 4.3 (with (4.6) and the history Fⁿ_t, p. 11)

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

theorem lemma_4_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (n : ℕ) (i : Fin N) :
    ∃ F : Filtration ℝ≥0 mΩ, (∀ t, F t = historySigma S n t) ∧
      (∀ t : ℝ≥0, Integrable (fun ω => Mhat S n ω t i) S.P) ∧
      Martingale (fun (t : ℝ≥0) ω => Mhat S n ω t i) F S.P ∧
      ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 ≤ t →
        sqJumpSum (fun s => Mhat S n ω s i) t = ENNReal.ofReal ((n : ℝ)⁻¹ * S.A n i ω t) := by sorry

end RankBasedSDI.LoadBalancing
