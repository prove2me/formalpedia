-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_pauli_four_outcome_povm
-- name    : QAlgorithms.Papers.Independent.Support21.P09.pauli_four_outcome_povm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:43:30.419885+00:00
-- url     : https://prove2.me/theorems/83643462-700d-4d42-9319-9d1b57445fcb
-- title:
--   Pauli-covariant four-outcome qubit POVM
-- statement:
--   Let $a,b\in\mathbb C$ satisfy $|a|^2+|b|^2=1/2$, and let
--
--   $$
--   M=\begin{pmatrix}a&a&b&b\b&-b&a&-a\end{pmatrix}.
--   $$
--
--   The four labeled nonzero column effects form a POVM. Conjugation by $I,Z,X,ZX$, the indicated projective representatives of $\mathbb Z_2\times\mathbb Z_2$, preserves this family. The ordinary subgroup $\widehat G=\langle X,Z\rangle\le U(2)$ is finite of order eight and has an ordinary monomial unitary representation $R$ with
--
--   $$
--   gM=MR(g)\quad(g\in\widehat G),\qquad ZM=MR_Z,\qquad XM=MR_X.
--   $$
--
--   Here $X$ exchanges the two coordinates, $Z=\operatorname{diag}(1,-1)$, $R_Z$ exchanges basis labels $0,1$ and $2,3$, and $R_X$ sends $(e_0,e_1,e_2,e_3)$ to $(e_2,-e_3,e_0,-e_1)$. The representation has these values on the corresponding generators. Labeled multiplicities remain present when some effects coincide, including degenerate parameter choices.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 8, Example 4: Pauli-covariant four-outcome qubit POVM

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF p.8, Example 4: four indexed effects, without an unjustified distinctness
hypothesis. The X,Z-generated ordinary lift has eight elements. -/
theorem pauli_four_outcome_povm (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    RankOnePOVM (qubitColumns a b) ∧
    EffectsCovariant pauliRepresentative (qubitColumns a b) ∧
    (pauliLift : Set (Matrix.unitaryGroup (Fin 2) ℂ)).Finite ∧ Nat.card pauliLift = 8 ∧
    pauliZFin * qubitColumns a b = qubitColumns a b * pauliRZ ∧
    pauliXFin * qubitColumns a b = qubitColumns a b * pauliRX ∧
    ∃ R : Rep pauliLift (Fin 4), UnitaryRep R ∧ (∀ g, Monomial (R g)) ∧
      MatrixIntertwines (naturalAction pauliLift) R (qubitColumns a b) ∧
      (∀ g, naturalAction pauliLift g = pauliXFin → R g = pauliRX) ∧
      (∀ g, naturalAction pauliLift g = pauliZFin → R g = pauliRZ) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
