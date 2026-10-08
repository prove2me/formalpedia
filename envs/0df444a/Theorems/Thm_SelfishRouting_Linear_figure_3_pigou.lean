-- Prove2me | Theorems.Thm_SelfishRouting_Linear_figure_3_pigou
-- name    : SelfishRouting.Linear.figure_3_pigou
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:16.31577+00:00
-- url     : https://prove2.me/theorems/e43022d3-c05c-4ac9-ad8a-cd40520ea8e4
-- title:
--   Figure 3 — Pigou's example: Nash cost $1$, optimal cost $3/4$, so $\rho=4/3$
-- statement:
--   The network of Figure 3 has one source–destination pair joined by two parallel links: the upper link has latency $\ell(x)=1$ and the lower link has latency $\ell(x)=x$; the rate is $1$. Then
--
--   1. the flow $(0,1)$, which puts the entire unit on the lower link, is at Nash equilibrium, and its cost is $1$;
--   2. the flow $(\tfrac12,\tfrac12)$, which spreads the flow evenly over the two links, is optimal, and its cost is $\tfrac34$.
--
--   Hence $\rho=C(f)/C(f^*)=4/3$ in this instance, so the constant $4/3$ of Theorem 4.5 cannot be lowered.
--
--   **Formalization Note** Route $0$ is the upper link and route $1$ the lower link; the incidence is the identity, there is one commodity, and the latencies are the linear latencies with $a=(0,1)$, $b=(1,0)$.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, pp. 11–12, Figure 3 and the paragraph introducing it

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

/-- Figure 3 (pp. 11–12): two parallel links with latencies `ℓ(x) = 1` (route 0) and
`ℓ(x) = x` (route 1), one commodity, rate 1. The flow `(0, 1)` is at Nash equilibrium with
cost 1, and the flow `(1/2, 1/2)` is optimal with cost 3/4, so `ρ = 4/3`. -/
theorem figure_3_pigou :
    SelfishRouting.Bicriteria.IsNashFlow (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (fun _ : Fin 2 => (0 : Fin 1))
        (linLatency ![0, 1] ![1, 0]) (fun _ => 1) ![0, 1] ∧
      SelfishRouting.Bicriteria.cost (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (linLatency ![0, 1] ![1, 0])
        ![0, 1] = 1 ∧
      IsOptimalFlow (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0)
        (fun _ : Fin 2 => (0 : Fin 1)) (linLatency ![0, 1] ![1, 0]) (fun _ => 1) ![1 / 2, 1 / 2] ∧
      SelfishRouting.Bicriteria.cost (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (linLatency ![0, 1] ![1, 0])
        ![1 / 2, 1 / 2] = 3 / 4 := by sorry

end SelfishRouting.Linear
