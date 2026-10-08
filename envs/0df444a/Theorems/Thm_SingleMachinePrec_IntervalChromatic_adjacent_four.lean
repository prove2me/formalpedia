-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalChromatic_adjacent_four
-- name    : SingleMachinePrec.IntervalChromatic.adjacent_four
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:28:57.135592+00:00
-- url     : https://prove2.me/theorems/a79940cf-5e1d-47c0-a128-437bc54581d8
-- title:
--   §4.2 — successive triple vertices are adjacent
-- statement:
--   Let $i<j<\ell<m$ be four endpoints in $[n]$. Each of
--   $$
--   u=(\{i,j\},\{j,\ell\}),\qquad v=(\{j,\ell\},\{\ell,m\})
--   $$
--   is an ordered incomparable pair of the canonical interval order $I_n$, and $u$ and $v$ are adjacent in $G_{I_n}$. Thus they cannot receive the same color in any proper coloring of the graph.
--
--   This is the adjacency assertion used in the four-point contradiction in the proof of Theorem 4.3. The proof's printed alternating-cycle justification names a different pair set; the stated adjacency is the formalized assertion.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, §4.2, proof of Theorem 4.3; DOI 10.1287/moor.1110.0512

import Definitions.Def_SingleMachinePrec_IntervalChromatic_CanonicalOrder

namespace SingleMachinePrec.IntervalChromatic

/-- Section 4.2, p. 658: successive triple vertices are adjacent. -/
theorem adjacent_four {n : ℕ} (i j l m : Fin n)
    (hij : i < j) (hjl : j < l) (hlm : l < m) :
    ∃ h₁ : SingleMachinePrec.Framework.Incomparable (I n) (endpointPair i j hij) (endpointPair j l hjl),
    ∃ h₂ : SingleMachinePrec.Framework.Incomparable (I n) (endpointPair j l hjl) (endpointPair l m hlm),
      G (I n)
        ⟨(endpointPair i j hij, endpointPair j l hjl), h₁⟩
        ⟨(endpointPair j l hjl, endpointPair l m hlm), h₂⟩ := by sorry

end SingleMachinePrec.IntervalChromatic
