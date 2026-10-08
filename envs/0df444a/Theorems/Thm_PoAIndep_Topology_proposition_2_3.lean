-- Prove2me | Theorems.Thm_PoAIndep_Topology_proposition_2_3
-- name    : PoAIndep.Topology.proposition_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:15.659703+00:00
-- url     : https://prove2.me/theorems/bb0f9631-37ad-4910-a342-5fc1e81de377
-- title:
--   Proposition 2.3, p. 6 — the cost of a feasible Nash flow is Σᵢ Lᵢ(f) rᵢ
-- statement:
--   The page notes after Proposition 2.2: "if $f$ is at Nash equilibrium then all $s_i$-$t_i$ flow paths ($s_i$-$t_i$ paths to which $f$ assigns a positive amount of flow) have equal latency, say $L_i(f)$."
--
--   Let $f$ be a flow at Nash equilibrium that is feasible for the instance $(G,r,\ell)$. Then there are numbers $L_1(f),\dots,L_k(f)$ such that every path $P$ with $f^i_P>0$ has latency $\ell_P(f)=L_i(f)$, and
--   $$C(f)=\sum_{i=1}^k L_i(f)\,r_i .$$
--
--   This expresses the cost of a Nash flow through the common latencies of its commodities; it is the first step in the proof of Lemma 3.7.
--
--   **Formalization Note.** The common latencies $L_i(f)$, defined in the sentence before the proposition, are carried as an existential witness.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 6, Proposition 2.3 (and the sentence defining L_i(f) before it)

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem proposition_2_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) (hfeas : IsFeasible I f)
    (hnash : IsNashFlow I f) :
    ∃ Lc : Fin I.k → ℝ, (∀ i P, 0 < f i P → pathLatency I f P = Lc i) ∧
      cost I f = ∑ i, Lc i * I.r i := by sorry

end PoAIndep.Topology
