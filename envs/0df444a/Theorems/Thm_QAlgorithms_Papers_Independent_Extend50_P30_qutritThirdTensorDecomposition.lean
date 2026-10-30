-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_qutritThirdTensorDecomposition
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.qutritThirdTensorDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:18:09.991784+00:00
-- url     : https://prove2.me/theorems/a5f3c449-d0fb-40cb-9440-50e3fcc62ce0
-- title:
--   Physical third-tensor qutrit decomposition
-- statement:
--   For $n\geq2$, let $N=\operatorname{span}_{\mathbb F_3}\{\mathbf1_3\}$ and $P=P_{\rm CSS(N)}^{\otimes n}$. Define $P_+=\Pi_{\rm sym}P\Pi_{\rm sym}$ and $P_-=\Pi_{\rm alt}P\Pi_{\rm alt}$. The ranges of $P_+$, $\Pi_{\rm sym}-P_+$, $P_-$, $\Pi_{\rm alt}-P_-$, and $(I+R((12)))/2-\Pi_{\rm sym}$ are five pairwise inequivalent irreducible physical Clifford modules. The first four occur once, with trivial or sign $S_3$ action; the last occurs with the standard two-dimensional $S_3$ action. An actual linear intertwiner identifies their direct sum with the three-block Hilbert space. All five defining operators are orthogonal projections.
--
--   $$
--   R(T_N)=3^nP,\quad\operatorname{rank}P=3^n,\quad\dim W_\pm=\frac{3^n\pm1}{2},\quad\mathcal H_n^{\otimes3}\cong W_+\oplus W_+^\perp\oplus W_-\oplus W_-^\perp\oplus(V_{(2,1)}\otimes\mathbb C^2).
--   $$
--
--   This gives the source's physical third-tensor qutrit decomposition in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 42, example-4.26-decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.42--43, Example 4.26: the complete physical Cliff(n,3) x S3 decomposition.
The last slice is the Schur (2,1) module; its standard S3 factor has dimension two.
The alternating compression, rather than the erroneous printed plus expansion, defines W_minus. -/
theorem qutritThirdTensorDecomposition (n : ℕ) (hn : 2 ≤ n) :
    Matrix.rank (qutritCSSProjector n) = 3 ^ n ∧
    tensorRelation n (cssRelation qutritDefect) = (3 : ℂ) ^ n • qutritCSSProjector n ∧
    Matrix.rank (qutritPieceProjector n 0) = (3 ^ n + 1) / 2 ∧
    Matrix.rank (qutritPieceProjector n 2) = (3 ^ n - 1) / 2 ∧
    (∀ i : Fin 5, (qutritPieceProjector n i).IsHermitian ∧
      qutritPieceProjector n i * qutritPieceProjector n i = qutritPieceProjector n i ∧
      IsCliffordIrreducible (qutritPiece n i)) ∧
    (∀ i j : Fin 5, i ≠ j → ¬ CliffordModulesEquivalent (qutritPiece n i) (qutritPiece n j)) ∧
    ∃ e : QutritDecomposition n ≃ₗ[ℂ] (QuditCopies 3 n 3 → ℂ),
      (∀ U : QuditOperator 3 n, IsClifford U → ∀ v w : QutritDecomposition n,
        (∀ i, (w i).val = (tensorPower 3 U).mulVec (v i).val) →
          e w = (tensorPower 3 U).mulVec (e v)) ∧
      (∀ p : Equiv.Perm (Fin 3), ∀ v w : QutritDecomposition n,
        (∀ i, (w i).val = if i.val < 2 then (v i).val else if i.val < 4 then
          (if Equiv.Perm.sign p = 1 then (1 : ℂ) else -1) • (v i).val else
          ∑ j : Fin 2, standardS3 p ⟨i.val - 4, by omega⟩ j •
            (v ⟨4 + j.val, by omega⟩).val) →
          e w = (permutationOperator 3 n 3 p).mulVec (e v)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
