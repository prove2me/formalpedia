-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P17_generalizedPauli_unital
-- name    : QAlgorithms.Papers.Independent.Frontier18.P17.generalizedPauli_unital
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:36:18.4493+00:00
-- url     : https://prove2.me/theorems/222757cf-ba45-4ffc-b423-af1fce222947
-- title:
--   Generalized Pauli channels are random unitary and unital
-- statement:
--   Let $d\ge1$, let $X_d|j\rangle=|j-1\bmod d\rangle$, and let $Z_d|j\rangle=e^{2\pi i j/d}|j\rangle$, with $j=0,\ldots,d-1$. For a probability array $p_{ij}\ge0$, $\sum_{i,j}p_{ij}=1$, set $U_{ij}=X_d^iZ_d^j$ and $\Pi_d(\rho)=\sum_{i,j}p_{ij}U_{ij}\rho U_{ij}^\dagger$. Then
--
--   $$U_{ij}\text{ is unitary for every }i,j,\qquad \Pi_d\text{ is a quantum channel},\qquad\Pi_d(I_d)=I_d.$$
--
--   Thus the displayed probability mixture is random unitary and unital. Uniform probabilities are not required; the $d=1$ case is the identity channel.
-- source:
--   Singular value decomposition and matrix reorderings in quantum information theory, arXiv:1011.1585v2, PDF p. 8, Example 5, Eqs.(60)–(62)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

namespace QAlgorithms.Papers.Independent.Frontier18.P17

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

/-- PDF p.8, Example 5, Eqs. (60)–(62): specified factors are unitary, so the
mixture is random unitary; it is a unital channel for every probability array. -/
theorem generalizedPauli_unital {d : ℕ} [NeZero d] (hd : 0 < d)
    (p : (Fin d × Fin d) → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    (∀ a : Fin d × Fin d, ((QAlgorithms.Papers.Independent.Information100.P34.weyl
      (d := d) (-(a.1.val : ZMod d)) (a.2.val : ZMod d)).submatrix
        (fun i : Fin d => (i.val : ZMod d)) (fun i : Fin d => (i.val : ZMod d))) ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    QAlgorithms.IsChannel (pauliChannel d p) ∧ pauliChannel d p 1 = 1 := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P17

end
