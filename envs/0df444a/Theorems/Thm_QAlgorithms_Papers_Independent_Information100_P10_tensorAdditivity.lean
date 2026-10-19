-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_tensorAdditivity
-- name    : QAlgorithms.Papers.Independent.Information100.P10.tensorAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:38:51.163983+00:00
-- url     : https://prove2.me/theorems/3f304775-fc5d-443d-ada4-7d850fdfd010
-- title:
--   Tensor-product additivity: property iv, Eqs.(33)–(34)
-- statement:
--   Let $\psi_1$ and $\psi_2$ be normalized pure states of $M_1$ and $M_2$ qubits, respectively, and identify their tensor product $\psi$ with the concatenated $M_1+M_2$ wire register. Then $\psi$ is normalized and, for every pair of independent unit-direction families $v_1,v_2$,
--
--   $$g(\psi,v_1\mathbin{\|}v_2)=\begin{pmatrix}g(\psi_1,v_1)&0\\0&g(\psi_2,v_2)\end{pmatrix},\qquad E(\psi_1\otimes\psi_2)=E(\psi_1)+E(\psi_2).$$
--
--   Both off-diagonal blocks vanish. The equality can be iterated for finite products; zero-qubit factors are allowed. This is the geometric factorization behind additivity.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 4, Tensor-product additivity: property iv, Eqs.(33)–(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF pp.4-5, Eqs.(33)-(34), property iv: block factorization for every direction family
and tensor-product additivity, including zero-qubit factors. -/
theorem tensorAdditivity {a b : ℕ} (psi : Ket a) (phi : Ket b)
    (hpsi : IsState psi) (hphi : IsState phi) :
    IsState (appendKet psi phi) ∧
    entanglementDistance (appendKet psi phi) =
      entanglementDistance psi + entanglementDistance phi ∧
    (∀ (v : Fin a → Direction) (w : Fin b → Direction),
      v ∈ directionDomain a → w ∈ directionDomain b →
      let g := orbitMetric (appendKet psi phi) (appendDirections v w)
      (∀ q r, g (Fin.castAdd b q) (Fin.castAdd b r) = orbitMetric psi v q r) ∧
      (∀ q r, g (Fin.natAdd a q) (Fin.natAdd a r) = orbitMetric phi w q r) ∧
      (∀ q r, g (Fin.castAdd b q) (Fin.natAdd a r) = 0) ∧
      (∀ q r, g (Fin.natAdd a q) (Fin.castAdd b r) = 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
