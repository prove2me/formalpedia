-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P37_quantum_coherent_region_square
-- name    : QAlgorithms.Papers.Independent.Support50.P37.quantum_coherent_region_square
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:55:05.273125+00:00
-- url     : https://prove2.me/theorems/d8c57b49-5e7c-4ce0-a67f-934c53e4cf36
-- title:
--   The full quantum/coherent bidirectional region square
-- statement:
--   Let $U$ be a fixed bipartite unitary or rectangular isometry between nonzero finite-dimensional registers held by Alice and Bob. Local quantum operations and local ancillas are free; every nonlocal call and every supplied EPR pair is counted. A positive signed rate produces a resource and a negative rate consumes it. Write $\mathcal R_{XY}(U;c_1,c_2,e)$ for simultaneous achievable forward $X$, backward $Y$, and ebit rates, where $X,Y\in\{\mathrm C,\mathrm{Co},\mathrm Q\}$ denote dephasing classical bits, coherent copying bits, and noiseless qubits. Achievability means that for every error tolerance $\epsilon>0$ and rate slack $\delta>0$, all sufficiently large $n$ admit a fixed finite protocol with at most $n$ uses of $U$, signed resource counts within $\delta$, and joint trace-distance error at most $\epsilon$, uniformly over normalized inputs and untouched reference systems. The protocol precedes the input; no external shared seed or catalyst is free.
--
--   For arbitrary $q_1,q_2,e\in\mathbb R$, define the four propositions
--   $$
--   \begin{aligned}
--   A&=\mathcal R_{\mathrm Q\mathrm Q}(U;q_1,q_2,e),\\
--   B&=\mathcal R_{\mathrm{Co}\mathrm Q}(U;2q_1,q_2,e-q_1),\\
--   C&=\mathcal R_{\mathrm Q\mathrm{Co}}(U;q_1,2q_2,e-q_2),\\
--   D&=\mathcal R_{\mathrm{Co}\mathrm{Co}}(U;2q_1,2q_2,e-q_1-q_2).
--   \end{aligned}
--   $$
--   Every edge of the square is an equivalence:
--   $$
--   (A\Longleftrightarrow B)\ \land\ (A\Longleftrightarrow C)\ \land\
--   (B\Longleftrightarrow D)\ \land\ (C\Longleftrightarrow D).
--   $$
--   This determines all four quantum/coherent bidirectional regions from any one of them. It is an asymptotic statement with counted startup and recycling; finite coherent teleportation's returned catalyst is not a free input.
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, PDF p. 9, §IV, Eq. (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19

open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Eq.(33): all four edges of the quantum/coherent rate-region square.
Rates Q1,Q2,E are signed. This is an asymptotic assertion: the finite coherent
teleportation catalyst must be generated and recycled through counted calls.
No finite zero-seed two-cobit equality is asserted. -/
theorem quantum_coherent_region_square (U : Resource) (hU : IsIsometricResource U)
    (Q1 Q2 E : ℝ) :
    (AchievesBidirectional U .quantum .quantum Q1 Q2 E ↔
      AchievesBidirectional U .coherent .quantum (2*Q1) Q2 (E-Q1)) ∧
    (AchievesBidirectional U .quantum .quantum Q1 Q2 E ↔
      AchievesBidirectional U .quantum .coherent Q1 (2*Q2) (E-Q2)) ∧
    (AchievesBidirectional U .coherent .quantum (2*Q1) Q2 (E-Q1) ↔
      AchievesBidirectional U .coherent .coherent (2*Q1) (2*Q2) (E-Q1-Q2)) ∧
    (AchievesBidirectional U .quantum .coherent Q1 (2*Q2) (E-Q2) ↔
      AchievesBidirectional U .coherent .coherent (2*Q1) (2*Q2) (E-Q1-Q2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P37

end
