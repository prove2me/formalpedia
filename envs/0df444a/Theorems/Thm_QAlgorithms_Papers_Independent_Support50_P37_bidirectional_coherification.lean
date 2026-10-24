-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P37_bidirectional_coherification
-- name    : QAlgorithms.Papers.Independent.Support50.P37.bidirectional_coherification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:51:07.614951+00:00
-- url     : https://prove2.me/theorems/d7d00842-b820-4463-9eac-061fb8feb10e
-- title:
--   Bidirectional coherification with arbitrary signed entanglement
-- statement:
--   Let $U$ be a fixed bipartite unitary or rectangular isometry between nonzero finite-dimensional registers held by Alice and Bob. Local quantum operations and local ancillas are free; every nonlocal call and every supplied EPR pair is counted. A positive signed rate produces a resource and a negative rate consumes it. Write $\mathcal R_{XY}(U;c_1,c_2,e)$ for simultaneous achievable forward $X$, backward $Y$, and ebit rates, where $X,Y\in\{\mathrm C,\mathrm{Co},\mathrm Q\}$ denote dephasing classical bits, coherent copying bits, and noiseless qubits. Achievability means that for every error tolerance $\epsilon>0$ and rate slack $\delta>0$, all sufficiently large $n$ admit a fixed finite protocol with at most $n$ uses of $U$, signed resource counts within $\delta$, and joint trace-distance error at most $\epsilon$, uniformly over normalized inputs and untouched reference systems. The protocol precedes the input; no external shared seed or catalyst is free.
--
--   For any $c_1,c_2\ge0$ and any $e\in\mathbb R$,
--   $$
--   \mathcal R_{\mathrm C\mathrm C}(U;c_1,c_2,e)
--   \quad\Longleftrightarrow\quad
--   \mathcal R_{\mathrm{Co}\mathrm{Co}}(U;c_1,c_2,e).
--   $$
--   This identifies the entire nonnegative communication quadrant, retaining the same signed entanglement rate, including zero communication rates.
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, PDF p. 3, Theorem 1, Eqs. (2)–(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19

open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Theorem 1, Eqs.(2)–(3), including the signed-E extensions on p.8.
The p.1 abstract is instantiated by this nonnegative-communication quadrant.
E<0 consumes nonnegative EPR counts of rate -E, as defined on p.2; the negative
EPR-copy exponent printed in Eq.(21) is not used as a tensor exponent. -/
theorem bidirectional_coherification (U : Resource) (hU : IsIsometricResource U)
    (C1 C2 E : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    AchievesBidirectional U .classical .classical C1 C2 E ↔
      AchievesBidirectional U .coherent .coherent C1 C2 E := by sorry

end QAlgorithms.Papers.Independent.Support50.P37

end
