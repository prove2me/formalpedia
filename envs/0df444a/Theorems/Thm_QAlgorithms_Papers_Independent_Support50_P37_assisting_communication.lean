-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P37_assisting_communication
-- name    : QAlgorithms.Papers.Independent.Support50.P37.assisting_communication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:52:10.810758+00:00
-- url     : https://prove2.me/theorems/70cf2783-f488-4a1e-b69c-3c245de73abe
-- title:
--   Assisting classical and coherent communication
-- statement:
--   Let $U$ be a fixed bipartite unitary or rectangular isometry between nonzero finite-dimensional registers held by Alice and Bob. Local quantum operations and local ancillas are free; every nonlocal call and every supplied EPR pair is counted. A positive signed rate produces a resource and a negative rate consumes it. Write $\mathcal R_{XY}(U;c_1,c_2,e)$ for simultaneous achievable forward $X$, backward $Y$, and ebit rates, where $X,Y\in\{\mathrm C,\mathrm{Co},\mathrm Q\}$ denote dephasing classical bits, coherent copying bits, and noiseless qubits. Achievability means that for every error tolerance $\epsilon>0$ and rate slack $\delta>0$, all sufficiently large $n$ admit a fixed finite protocol with at most $n$ uses of $U$, signed resource counts within $\delta$, and joint trace-distance error at most $\epsilon$, uniformly over normalized inputs and untouched reference systems. The protocol precedes the input; no external shared seed or catalyst is free.
--
--   Let $c_1,c_2\ge0$ and $e\in\mathbb R$. Both of the following chains hold, with every link an equivalence:
--   $$
--   \begin{gathered}
--   \mathcal R_{\mathrm C\mathrm C}(U;c_1,-c_2,e)
--   \Longleftrightarrow\mathcal R_{\mathrm C\mathrm C}(U;c_1,0,e)
--   \Longleftrightarrow\mathcal R_{\mathrm{Co}\mathrm{Co}}(U;c_1,0,e)
--   \Longleftrightarrow\mathcal R_{\mathrm{Co}\mathrm{Co}}(U;c_1,-c_2,e+c_2),\\[4pt]
--   \mathcal R_{\mathrm C\mathrm C}(U;-c_1,-c_2,e)
--   \Longleftrightarrow\mathcal R_{\mathrm C\mathrm C}(U;0,0,e)
--   \Longleftrightarrow\mathcal R_{\mathrm{Co}\mathrm{Co}}(U;-c_1,-c_2,e+c_1+c_2).
--   \end{gathered}
--   $$
--   Classical assistance does not enlarge these communication or entanglement tradeoffs. Coherent assistance contributes its displayed entanglement increment. The formal statement conjoins the five adjacent equivalences.
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, PDF p. 8, Theorem 2, Eqs. (23)–(29)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19

open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Theorem 2, Eqs.(23)–(29): both displayed chains, as five separate
edge equivalences. The nonnegative assisting amounts C1,C2 occur with negative
signed communication rates. E is arbitrary, including entanglement consumption. -/
theorem assisting_communication (U : Resource) (hU : IsIsometricResource U)
    (C1 C2 E : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    (AchievesBidirectional U .classical .classical C1 (-C2) E ↔
      AchievesBidirectional U .classical .classical C1 0 E) ∧
    (AchievesBidirectional U .classical .classical C1 0 E ↔
      AchievesBidirectional U .coherent .coherent C1 0 E) ∧
    (AchievesBidirectional U .coherent .coherent C1 0 E ↔
      AchievesBidirectional U .coherent .coherent C1 (-C2) (E+C2)) ∧
    (AchievesBidirectional U .classical .classical (-C1) (-C2) E ↔
      AchievesBidirectional U .classical .classical 0 0 E) ∧
    (AchievesBidirectional U .classical .classical 0 0 E ↔
      AchievesBidirectional U .coherent .coherent (-C1) (-C2) (E+C1+C2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P37

end
