-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P30_exponentialRepresentation_continuous
-- name    : QAlgorithms.Papers.Independent.Next46.P30.exponentialRepresentation_continuous
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:19:24.938175+00:00
-- url     : https://prove2.me/theorems/0dd27dc4-54c0-4785-8da2-a0cfd58d7aa5
-- title:
--   Joint continuity of the L² phase-multiplication action
-- statement:
--   Let $G=L^2([0,1],\mathbb R)$ be the additive real Hilbert space and let $H=L^2([0,1],\mathbb C)$ be the complex Hilbert space, both for Lebesgue measure and with their norm topologies. Elements are equivalence classes modulo equality almost everywhere. Define the particular action $\pi(f)\xi=e^{if}\xi$, with multiplication interpreted almost everywhere.
--
--   The action map is jointly continuous:
--
--   $$
--   \pi:G\times H\longrightarrow H,\qquad(f,\xi)\longmapsto e^{if}\xi,\quad\text{is continuous}.
--   $$
--
--   This is continuity of the action for all Hilbert vectors in the sense of Definition 1.1. It supplies the continuity assertion used in the paper’s main example.
-- source:
--   A non-smooth continuous unitary representation of a Banach-Lie group, arXiv:0811.4234v1, PDF p. 3, Proposition 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Next46.P30

/-- Proposition 2.1 (arXiv:0811.4234v1, PDF p. 3): continuity means joint continuity
of the action G × H → H, with no boundedness restriction on the Hilbert vector. -/
theorem exponentialRepresentation_continuous :
    Continuous (fun z : GroupSpace × HilbertSpace => phaseAction z.1 z.2) := by sorry

end QAlgorithms.Papers.Independent.Next46.P30

end
