-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma7_expansionNorm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma7_expansionNorm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:49:43.724534+00:00
-- url     : https://prove2.me/theorems/f64da9f7-863d-4386-8a7b-858db5bc4347
-- title:
--   Lemma 7 (Norm inequality using expansion property)
-- statement:
--   For an $n$-qubit Hermitian operator $H$ with real Pauli coefficients $\alpha_P$, write $\operatorname{supp}P$ for its nonidentity wires. The expansion property $(c_e,d_e)$ means that for each set $S$ of $d_e$ wires,
--   $$\#\{P:\alpha_P\ne0,\ S\subseteq\operatorname{supp}P\ \text{or}\ \operatorname{supp}P\subseteq S\}\le c_e.$$
--   The identity term is included in this count.
--
--   Assume $n\ge1$, $c_e\ge1$, $1\le d_e\le n$, and write $r=2d_e/(d_e+1)$. For any integer $a\ge1$,
--   $$\sum_i\sqrt{\sum_{|P|=a,\,P_i\ne I}\alpha_P^2}\ge c_e^{-1/(2d_e)}\left(\sum_{|P|=a}|\alpha_P|^r\right)^{1/r}.$$
--   This turns a sum of local Euclidean coefficient norms into a global coefficient norm with exponent below two. Empty weight slices have zero on both sides.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 28, Lemma 7 (Norm inequality using expansion property)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 7, paper p.28, A78; an empty homogeneous slice gives zero on both sides. -/
theorem lemma7_expansionNorm (n de q : ℕ) (hn : 1 ≤ n) (hde : 1 ≤ de)
    (hden : de ≤ n) (hq : 1 ≤ q) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hexp : HasExpansion H ce de) :
    sliceMass q (expansionExponent de) H / Real.rpow ce (1 / (2 * (de : ℝ))) ≤
      ∑ i : Fin n, Real.sqrt
        (∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q ∧ P i ≠ 0),
          coefficient H P ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
