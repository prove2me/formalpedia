-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P37_average_error_coherification
-- name    : QAlgorithms.Papers.Independent.Support50.P37.average_error_coherification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:56:26.843988+00:00
-- url     : https://prove2.me/theorems/4fe58fc7-bf2b-4d45-9fde-54bfc3f9e7a8
-- title:
--   Uniform average error suffices for E=0 coherification
-- statement:
--   Let $U$ be a fixed bipartite unitary or isometry between nonzero finite-dimensional registers, and let $c_1,c_2\ge0$. Suppose finite protocols $P_n$, using at most $n$ calls to $U$ and free local operations only, transmit independent uniform classical messages of lengths $m_1(n)$ and $m_2(n)$, with $m_i(n)\le n c_i$ and $m_i(n)/n\to c_i$. Neither the protocol, its schedule, nor its register dimensions depends on the message pair. No external entanglement, shared random seed, side communication, or catalyst is supplied.
--
--   If the uniform average joint decoding success tends to one, then the same rates are achievable coherently:
--   $$
--   \frac{1}{2^{m_1(n)+m_2(n)}}\sum_{a,b}
--    \Pr[P_n(a,b)=(b,a)]\longrightarrow1
--   \quad\Longrightarrow\quad
--   U\succeq c_1\ \mathrm{cobits}(\rightarrow)+c_2\ \mathrm{cobits}(\leftarrow).
--   $$
--   Here $a$ and $b$ range over all respective bit strings, and $(b,a)$ specifies Alice's and Bob's decoded outputs. The coherent conclusion has vanishing joint trace-distance error uniformly over normalized quantum inputs and untouched references, without supplied entanglement. This states the $e=0$ strengthening actually used in the construction, rather than an unspecified resource-assisted generalization.
-- source:
--   Bidirectional coherent classical communication, arXiv:quant-ph/0412126v3, PDF p. 12, Note [14], with §III p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P37

open QAlgorithms.Papers.Independent.Support21.P19

open QAlgorithms.Papers.Independent.Renew46.P34 (rateConstraint)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, norm-squared identity for Gamma_00, and note [14] on p.12.
In the E=0 construction, a vanishing uniform average classical error suffices for
reference-uniform coherent transmission at the same rates, without an external seed. -/
theorem average_error_coherification (U : Resource) (hU : IsIsometricResource U)
    (C1 C2 : ℝ) (h : AchievesAverageClassical U C1 C2) :
    AchievesBidirectional U .coherent .coherent C1 C2 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P37

end
