-- Prove2me | Theorems.Thm_RunIntersect_Strict_strict_cycleHg
-- name    : RunIntersect.Strict.strict_cycleHg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:30.534086+00:00
-- url     : https://prove2.me/theorems/331e4287-e7e5-46a0-9825-583fdfae380f
-- title:
--   Proof of Proposition 5, p. 1019 — for a chordless cycle, MP ⊂ MP^RI
-- statement:
--   Let $t\ge 3$ and let $v_1,\dots,v_t$ be distinct nodes. For the graph $C_t$ consisting of the chordless cycle with edges $\{v_i,v_{i+1}\}$ (indices mod $t$), the running intersection relaxation strictly contains the multilinear polytope:
--   $$\mathrm{MP}_{C_t}\subsetneq\mathrm{MP}^{\mathrm{RI}}_{C_t}.$$
--
--   This is the first of the two cases of the proof of Proposition 5 (the subhypergraph induced by a shortest β-cycle is exactly the cycle).
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, proof of Proposition 5, second paragraph (Padberg [25])

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Proof of Proposition 5, p. 1019: for a chordless cycle of length `t ≥ 3`, `MP ⊂ MP^RI` (strictly). -/
theorem strict_cycleHg {α : Type*} [Fintype α] [DecidableEq α] (t : ℕ) (ht : 3 ≤ t)
    (v : Fin t → α) (hv : Function.Injective v) :
    MP (cycleHg t v ht hv) ⊂ MPRI (cycleHg t v ht hv) := by sorry

end RunIntersect.Strict
