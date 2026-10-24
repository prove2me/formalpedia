-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P37_signed_classical_coherent_regions
-- name    : QAlgorithms.Papers.Independent.Support50.P37.signed_classical_coherent_regions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:54:11.535347+00:00
-- url     : https://prove2.me/theorems/b83fcb0f-9130-4fc9-b7ab-ae91225a9fb9
-- title:
--   Classical/coherent mapping in every signed quadrant
-- statement:
--   Let $U$ be a fixed bipartite unitary or rectangular isometry between nonzero finite-dimensional registers held by Alice and Bob. Local quantum operations and local ancillas are free; every nonlocal call and every supplied EPR pair is counted. A positive signed rate produces a resource and a negative rate consumes it. Write $\mathcal R_{XY}(U;c_1,c_2,e)$ for simultaneous achievable forward $X$, backward $Y$, and ebit rates, where $X,Y\in\{\mathrm C,\mathrm{Co},\mathrm Q\}$ denote dephasing classical bits, coherent copying bits, and noiseless qubits. Achievability means that for every error tolerance $\epsilon>0$ and rate slack $\delta>0$, all sufficiently large $n$ admit a fixed finite protocol with at most $n$ uses of $U$, signed resource counts within $\delta$, and joint trace-distance error at most $\epsilon$, uniformly over normalized inputs and untouched reference systems. The protocol precedes the input; no external shared seed or catalyst is free.
--
--   For all signed real rates $c_1,c_2,e$,
--   $$
--   \mathcal R_{\mathrm C\mathrm C}(U;c_1,c_2,e)
--   \quad\Longleftrightarrow\quad
--   \mathcal R_{\mathrm{Co}\mathrm{Co}}
--    (U;c_1,c_2,e-\min(c_1,0)-\min(c_2,0)).
--   $$
--   Thus the classical region $\mathrm{CCE}$ determines the coherent region $\mathrm{CoCoE}$ in every quadrant. For example, consumed communication rates $c_1=-a,c_2=-b$, with $a,b\ge0$, shift the coherent entanglement coordinate to $e+a+b$.
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, PDF p. 9, §IV, Eq. (31)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19

open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Eq.(31): mapping of the full signed CCE and CoCoE regions.
The preceding prose prints CCC; the displayed formula and the defined region use CCE.
All three coordinates are real, and consumed cobits increase the E coordinate. -/
theorem signed_classical_coherent_regions (U : Resource) (hU : IsIsometricResource U)
    (C1 C2 E : ℝ) :
    AchievesBidirectional U .classical .classical C1 C2 E ↔
      AchievesBidirectional U .coherent .coherent C1 C2
        (E-min C1 0-min C2 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P37

end
