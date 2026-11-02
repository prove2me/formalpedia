-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_nearestBoundedError_inP
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.nearestBoundedError_inP
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:17:01.231527+00:00
-- url     : https://prove2.me/theorems/56e54a64-54c4-404a-9099-92442c8aa5e0
-- title:
--   Bounded-error nearest-neighbour matchgate languages lie in deterministic P
-- statement:
--   For each input length, fix one effectively uniform nearest-neighbour matchgate circuit, with enough wires for the computational-basis input and zero workspace, and one existing output wire. Every local parity block is unitary and the even and odd determinants agree. Suppose the output bit is correct with probability at least $2/3$ on every input. Then the decided language belongs to deterministic polynomial time:
--
--   $$\mathcal V^{\mathrm{bounded}}_{\mathrm{n.n.}}\subseteq\mathrm P.$$
--
--   Here the left class is exactly the class of languages admitted by those circuit families, and $\mathrm P$ is defined by a characteristic function computed by an actual polynomial-time finite Turing machine. This is the bounded-error specialization of strong simulation, using only constant precision.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 3, Section 1 consequence: bounded-error nearest-neighbour matchgate decision problems lie in P

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: bounded-error nearest-neighbour matchgate decision languages are
in deterministic P. The class definitions fix one circuit per input length,
computational-basis inputs, uniform finite descriptions and the 2/3 gap. -/
theorem nearestBoundedError_inP :
    {L : Set Str | InBoundedMatchgate 1 L} ⊆ {L : Set Str | InP L} := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
