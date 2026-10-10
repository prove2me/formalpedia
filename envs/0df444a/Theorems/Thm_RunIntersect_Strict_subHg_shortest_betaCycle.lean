-- Prove2me | Theorems.Thm_RunIntersect_Strict_subHg_shortest_betaCycle
-- name    : RunIntersect.Strict.subHg_shortest_betaCycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:38.659047+00:00
-- url     : https://prove2.me/theorems/ab78ae98-990a-4e51-aade-00712ba0436f
-- title:
--   Proof of Proposition 5, p. 1019 — G_{V(C)} of a shortest β-cycle C is a chordless cycle, possibly enclosed by the edge V(C)
-- statement:
--   Let $G$ be a hypergraph and let $C=v_1,e_1,\dots,v_t,e_t,v_1$ be a β-cycle of $G$ of minimum length $t$ among all β-cycles of $G$. Write $V(C)=\{v_1,\dots,v_t\}$ and $\tilde E=\{e\cap V(C):e\in E(C)\}$. Then
--   1. $e_i\cap V(C)=\{v_i,v_{i+1}\}$ for every $i$ (indices mod $t$), so $\tilde E$ is the edge set of the chordless cycle on $v_1,\dots,v_t$;
--   2. the subhypergraph induced by $V(C)$ is either that chordless cycle or that chordless cycle enclosed by the edge $V(C)$:
--   $$E(G_{V(C)})=\tilde E\quad\text{or}\quad E(G_{V(C)})=\tilde E\cup\{V(C)\}.$$
--
--   This is the structural step of the proof of Proposition 5; it reduces the proposition to two explicit families of hypergraphs.
--
--   **Formalization Note** The cycle is $0$-indexed: $v_i\in e_j$ iff $j=i$ or $j+1\equiv i\pmod t$. Minimality is over all β-cycles of $G$ of every length; for a β-cycle that is not shortest the conclusion can fail.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, proof of Proposition 5, second and third paragraphs

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Proof of Proposition 5, p. 1019: for a β-cycle `C` of minimum length `t`, every edge `e_i` of `C`
meets `V(C)` in `{v_i, v_{i+1}}`, and `G_{V(C)}` is the chordless cycle on `V(C)`, possibly enclosed by
the edge `V(C)`. -/
theorem subHg_shortest_betaCycle {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α)
    (t : ℕ) (v : Fin t → α) (e : Fin t → Finset α) (hC : IsBetaCycle G t v e)
    (hmin : ∀ (s : ℕ) (v' : Fin s → α) (e' : Fin s → Finset α), IsBetaCycle G s v' e' → t ≤ s) :
    (∀ i, e i ∩ Finset.univ.image v = {v i, v (cycSucc i)}) ∧
      (subHg G (Finset.univ.image v) = cycleHg t v hC.1 hC.2.1 ∨
        subHg G (Finset.univ.image v) = enclosedCycleHg t v hC.1 hC.2.1) := by sorry

end RunIntersect.Strict
