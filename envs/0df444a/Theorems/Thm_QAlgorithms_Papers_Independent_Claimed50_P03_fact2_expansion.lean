-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_fact2_expansion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.fact2_expansion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:43:57.715665+00:00
-- url     : https://prove2.me/theorems/d3328802-a739-4e06-af26-075e4c9c9aaa
-- title:
--   Fact 2
-- statement:
--   For an $n$-qubit Hermitian operator $H$ with real Pauli coefficients $\alpha_P$, write $\operatorname{supp}P$ for its nonidentity wires. The expansion property $(c_e,d_e)$ means that for each set $S$ of $d_e$ wires,
--   $$\#\{P:\alpha_P\ne0,\ S\subseteq\operatorname{supp}P\ \text{or}\ \operatorname{supp}P\subseteq S\}\le c_e.$$
--   The identity term is included in this count.
--
--   Let $n,k,d\ge1$. If $H=\sum_jh_j$, each Hermitian $h_j$ is supported on at most $k$ wires and each wire belongs to at most $d$ term supports, then
--   $$c_e=4^k d,\qquad d_e=1.$$
--   This gives an expansion guarantee from bounded participation, including a possible scalar component.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 18, Fact 2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Fact 2, paper p.18. Identity support is included in the A2 count. -/
theorem fact2_expansion (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hdeg : HasBoundedDegree k d H) :
    HasExpansion H ((4 : ℝ) ^ k * (d : ℝ)) 1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
