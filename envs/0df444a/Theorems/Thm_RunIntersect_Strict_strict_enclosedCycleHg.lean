-- Prove2me | Theorems.Thm_RunIntersect_Strict_strict_enclosedCycleHg
-- name    : RunIntersect.Strict.strict_enclosedCycleHg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:11.647458+00:00
-- url     : https://prove2.me/theorems/027dcd10-a2c4-478a-b405-7a072bd69962
-- title:
--   Proof of Proposition 5, p. 1019 — for a chordless cycle enclosed by the edge V(C), MP ⊂ MP^RI
-- statement:
--   Let $t\ge 3$ and let $v_1,\dots,v_t$ be distinct nodes. Let $H_t$ be the hypergraph on $\{v_1,\dots,v_t\}$ whose edges are the cycle edges $\{v_i,v_{i+1}\}$ (indices mod $t$) together with the edge $\bar e=\{v_1,\dots,v_t\}$. Then
--   $$\mathrm{MP}_{H_t}\subsetneq\mathrm{MP}^{\mathrm{RI}}_{H_t}.$$
--
--   This is the second case of the proof of Proposition 5 (the subhypergraph induced by a shortest β-cycle is the cycle together with the edge $V(C)$).
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, proof of Proposition 5, third paragraph

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Proof of Proposition 5, p. 1019: for a chordless cycle of length `t ≥ 3` enclosed by the edge
`V(C)`, `MP ⊂ MP^RI` (strictly). -/
theorem strict_enclosedCycleHg {α : Type*} [Fintype α] [DecidableEq α] (t : ℕ) (ht : 3 ≤ t)
    (v : Fin t → α) (hv : Function.Injective v) :
    MP (enclosedCycleHg t v ht hv) ⊂ MPRI (enclosedCycleHg t v ht hv) := by sorry

end RunIntersect.Strict
