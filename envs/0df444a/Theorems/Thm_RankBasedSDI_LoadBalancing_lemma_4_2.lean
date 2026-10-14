-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_lemma_4_2
-- name    : RankBasedSDI.LoadBalancing.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:19.470715+00:00
-- url     : https://prove2.me/theorems/a1891bc6-af95-46aa-bb0d-96fa30b33115
-- title:
--   Lemma 4.2: Skorokhod's lemma, complementarity characterises $(x,z)=\Gamma(y)$
-- statement:
--   Let $y\in D(\mathbb R_+,\mathbb R)$ and $x,z\in D(\mathbb R_+,\mathbb R_+)$ satisfy $x=y+z$. Then the following are equivalent:
--
--   1. $z$ is nondecreasing and $\int_{[0,\infty)}x(t)\,dz(t)=0$, with the convention $z(0-)=0$;
--   2. $(x,z)=\Gamma(y)$, i.e. for every $t\ge0$,
--
--   $$
--   z(t)=\sup_{s\in[0,t]}y^-(s),\qquad x(t)=y(t)+\sup_{s\in[0,t]}y^-(s),
--   $$
--
--   where $y^-=\max(-y,0)$.
--
--   This is Skorokhod's lemma for the one-dimensional reflection map. In the paper it identifies the scaled queue length and idle time as the Skorokhod map of the netput process (4.10), and it identifies the limit $(X_i,L_i)=\Gamma(U_i)$.
--
--   **Formalization Note** Càdlàg is the referenced `IsCadlag`: right-continuous on $[0,\infty)$ with left limits on $(0,\infty)$. Nonnegativity and $x=y+z$ are required on $[0,\infty)$. The integral condition is `StieltjesComplementary`, a `lintegral` against the Stieltjes measure of $z$ extended by $0$ on $(-\infty,0)$, so $z(0)$ is an atom at $0$.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 11, Lemma 4.2 and the definition of Γ

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace RankBasedSDI.LoadBalancing

theorem lemma_4_2 (y x z : ℝ → ℝ) (hy : IsCadlag y) (hx : IsCadlag x) (hz : IsCadlag z)
    (hx0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ x t) (hz0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ z t)
    (hxyz : ∀ t : ℝ, 0 ≤ t → x t = y t + z t) :
    (MonotoneOn z (Set.Ici 0) ∧ StieltjesComplementary x z) ↔
      ∀ t : ℝ, 0 ≤ t → x t = y t + skorokhodReg y t ∧ z t = skorokhodReg y t := by sorry

end RankBasedSDI.LoadBalancing
