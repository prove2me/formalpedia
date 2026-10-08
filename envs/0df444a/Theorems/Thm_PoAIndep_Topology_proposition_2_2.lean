-- Prove2me | Theorems.Thm_PoAIndep_Topology_proposition_2_2
-- name    : PoAIndep.Topology.proposition_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:08.941588+00:00
-- url     : https://prove2.me/theorems/328a18ba-7569-4ef6-b6bd-0cba9a480935
-- title:
--   Proposition 2.2, p. 6 — f is a Nash flow iff every used path of a commodity is a shortest path
-- statement:
--   Let $(G,r,\ell)$ be an instance (latency functions nonnegative, differentiable and nondecreasing on $[0,\infty)$) and let $f$ be a flow. Then $f$ is at Nash equilibrium in the sense of Definition 2.1 if and only if, for every commodity $i$ and all simple $s_i$–$t_i$ paths $P_1,P_2$ with $f^i_{P_1}>0$,
--   $$\ell_{P_1}(f)\le\ell_{P_2}(f).$$
--
--   In words: in a Nash flow all flow travels on minimum-latency paths. The page derives it from Definition 2.1 by letting the moved amount $\delta$ tend to $0$, using continuity and monotonicity of the edge latencies. It is the working characterization of Nash flows used in Proposition 2.3 and Lemma 3.7.
--
--   **Formalization Note.** The hypothesis that $f$ is a flow (nonnegative, supported on simple $s_i$–$t_i$ paths) is the paper's standing setting; feasibility is not needed.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 6, Proposition 2.2 (with the sentence preceding it on p. 5)

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem proposition_2_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) :
    IsNashFlow I f ↔
      ∀ (i : Fin I.k) (P₁ P₂ : List E),
        IsSimplePath I.src I.tgt P₁ (I.s i) (I.t i) →
        IsSimplePath I.src I.tgt P₂ (I.s i) (I.t i) →
        0 < f i P₁ → pathLatency I f P₁ ≤ pathLatency I f P₂ := by sorry

end PoAIndep.Topology
