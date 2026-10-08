-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_prop3_le_of_tendsto
-- name    : StochIneqPO.Comparison.prop3_le_of_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:28.321979+00:00
-- url     : https://prove2.me/theorems/3db208fa-8b99-4bfe-b2a5-9c3b64dc7370
-- title:
--   Proposition 3 — the stochastic order is preserved under weak convergence
-- statement:
--   Let $E$ be a partially ordered Polish space, and let $(P_m)_{m \ge 1}$, $(Q_m)_{m \ge 1}$ be sequences of probability measures on $E$ converging weakly to probability measures $P$ and $Q$ respectively. If
--   $$P_m \prec Q_m \qquad \text{for all } m,$$
--   then $P \prec Q$.
--
--   In other words, the set $\{(P,Q) : P \prec Q\}$ is closed for the weak topology; the paper uses this to conclude that $\prec$ is a closed order on the space of probability measures.
--
--   **Formalization Note** Weak convergence is convergence in Mathlib's topology on `ProbabilityMeasure E` (integrals of bounded continuous functions converge). The sequences are indexed from $0$ instead of $1$.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proposition 3, p. 903 (PDF p. 5)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Filter Topology

theorem prop3_le_of_tendsto {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (Pm Qm : ℕ → ProbabilityMeasure E) (P Q : ProbabilityMeasure E)
    (hP : Tendsto Pm atTop (𝓝 P)) (hQ : Tendsto Qm atTop (𝓝 Q))
    (h : ∀ m, StochLE (Pm m : Measure E) (Qm m : Measure E)) :
    StochLE (P : Measure E) (Q : Measure E) := by sorry

end StochIneqPO.Comparison
