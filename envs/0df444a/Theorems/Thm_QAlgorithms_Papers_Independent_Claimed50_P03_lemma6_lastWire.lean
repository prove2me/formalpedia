-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma6_lastWire
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma6_lastWire
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:48:58.505979+00:00
-- url     : https://prove2.me/theorems/72a97086-e28f-4528-862f-e54043706efd
-- title:
--   Lemma 6 (A characterization of expansion)
-- statement:
--   For an $n$-qubit Hermitian operator $H$ with real Pauli coefficients $\alpha_P$, write $\operatorname{supp}P$ for its nonidentity wires. The expansion property $(c_e,d_e)$ means that for each set $S$ of $d_e$ wires,
--   $$\#\{P:\alpha_P\ne0,\ S\subseteq\operatorname{supp}P\ \text{or}\ \operatorname{supp}P\subseteq S\}\le c_e.$$
--   The identity term is included in this count.
--
--   Assume $n\ge1$, $c_e\ge1$, $1\le d_e\le n$. For any permutation $\pi$ of the wires and every one-based index $i\in\{1,\ldots,n\}$,
--   $$\#\{P:\alpha_P\ne0,\ P_{\pi(i)}\ne I,\ P_{\pi(j)}=I\text{ for all }j>i\}\le c_e i^{d_e-1}.$$
--   This controls the growth of terms classified by their last nonidentity wire.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 28, Lemma 6 (A characterization of expansion)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 6, paper p.28, A72. Lean index i denotes the source's i+1;
the power is applied to i.val+1, never to the zero-based index. -/
theorem lemma6_lastWire (n de : ℕ) (hn : 1 ≤ n) (hde : 1 ≤ de) (hden : de ≤ n)
    (ce : ℝ) (hce : 1 ≤ ce) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian)
    (hexp : HasExpansion H ce de) (pi : Equiv.Perm (Fin n)) (i : Fin n) :
    ((Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      P (pi i) ≠ 0 ∧ ∀ j : Fin n, i < j → P (pi j) = 0).card : ℝ) ≤
      ce * ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
