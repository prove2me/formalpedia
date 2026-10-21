-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_fact1_expansion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.fact1_expansion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:43:16.11299+00:00
-- url     : https://prove2.me/theorems/55020723-2be8-47f7-b830-e0c1129e9d20
-- title:
--   Fact 1 (Expansion property for general 𝑘-local Hamiltonian). Any Hamiltonian given by a sum of 𝑘-qubit observables has expansion coefficient 4𝑘 and expansion dimension 𝑘. ∑︀
-- statement:
--   For an $n$-qubit Hermitian operator $H$ with real Pauli coefficients $\alpha_P$, write $\operatorname{supp}P$ for its nonidentity wires. The expansion property $(c_e,d_e)$ means that for each set $S$ of $d_e$ wires,
--   $$\#\{P:\alpha_P\ne0,\ S\subseteq\operatorname{supp}P\ \text{or}\ \operatorname{supp}P\subseteq S\}\le c_e.$$
--   The identity term is included in this count.
--
--   For $n,k\ge1$, every $k$-local $H$ satisfies
--   $$c_e=4^k,\qquad d_e=k.$$
--   This supplies the general-locality instance of the expansion framework. When $k>n$ there are no $k$-subsets, so this particular expansion predicate is vacuous; downstream characterizations separately require $d_e\le n$.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 18, Fact 1 (Expansion property for general 𝑘-local Hamiltonian). Any Hamiltonian given by a sum of 𝑘-qubit observables has expansion coefficient 4𝑘 and expansion dimension 𝑘. ∑︀

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Fact 1, paper p.18, A2. For k>n there are no k-subsets, as in the source. -/
theorem fact1_expansion (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H) :
    HasExpansion H ((4 : ℝ) ^ k) k := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
