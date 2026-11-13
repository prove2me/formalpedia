-- Prove2me | Theorems.Thm_RepellingPairs_cost_inequality_of_trivial_pair
-- name    : RepellingPairs.cost_inequality_of_trivial_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:51:24.763236+00:00
-- url     : https://prove2.me/theorems/dc579776-5a06-41d0-a00e-d111910c6f6e
-- title:
--   §3.4, pp.13–14 — Property 3 fails when F has a trivial unit and F′ no trivial path there
-- statement:
--   The case of §3.4's cost inequality in which the integral flow $F$ contains a unit on a trivial pair $(t,t)$ and $F'$ has no trivial path at $t$: in an Okamura–Seymour instance with a Kalmanson metric $D$ and a $D$-good shortest path structure $P$, for integral flows $F$, $F'$ with Properties 2, 4 and 5, $\sum F' D \le \sum F D$.
--
--   The remaining case of the same inequality (no trivial unit, or a trivial path of $F'$ at the same terminal) is reduced to Claim 9, Lemma 10 and the uniqueness of configurations from their metrics; this statement isolates the case that Claim 9 as printed does not cover, where units on trivial pairs change the degrees at $t$ without changing any cut.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, pp. 13-14, "Completing the proof of Theorem 1", the case of a unit of F on a trivial pair

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_IntegralFlow

set_option autoImplicit false

namespace RepellingPairs

universe u v

theorem cost_inequality_of_trivial_pair {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h4 : Property4 F F') (h5 : Property5 P F)
    (t : Fin k) (ht : (t, t) ∈ F) (hF' : ∀ q ∈ F', ¬ (q.src = t ∧ q.tgt = t)) :
    PathFlow.cost D F' ≤ DesignatedFlow.cost D F := by sorry

end RepellingPairs
