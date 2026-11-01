-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_channelFidelity_identity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.channelFidelity_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:24:29.427518+00:00
-- url     : https://prove2.me/theorems/7fa38f0b-5d67-413b-936c-f621bc7e5ca8
-- title:
--   Qubit channel fidelity in Kraus and Liouville form
-- statement:
--   Let $A_1,\ldots,A_4$ be $2\times2$ complex matrices with $\sum_k A_k^\dagger A_k=I$, and put $\mathcal E(\rho)=\sum_k A_k\rho A_k^\dagger$. Zero Kraus operators are allowed. Let $\rho_{\mathcal E}=(\mathcal E\otimes I)(|\Psi\rangle\langle\Psi|)$, where $|\Psi\rangle=(|00\rangle+|11\rangle)/\sqrt2$. Let $L_{ij}=\tfrac12\operatorname{Tr}(\sigma_i\mathcal E(\sigma_j))$, with $\sigma_0=I$ and the usual three Pauli matrices. Then
--
--   $$F_E=\langle\Psi|\rho_{\mathcal E}|\Psi\rangle=\frac14\sum_{k=1}^4|\operatorname{Tr}A_k|^2=\frac14\operatorname{Tr}L.$$
--
--   The normalized Choi trace is one; it is not the Liouville trace appearing in this identity. The oscillator implementation needs no finite Fock cutoff for this finite effective-channel identity.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 3, §I B (1.11): channel fidelity in Kraus and Liouville form

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3 (1.11): both Kraus and Liouville formulas, under the squared overlap convention. -/
theorem channelFidelity_identity (A : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsKrausFamily A) :
    QuditFidelity.entanglementFidelity 2 (by decide) (krausApply A) =
      (∑ k, Complex.normSq ((A k).trace)) / 4 ∧
    QuditFidelity.entanglementFidelity 2 (by decide) (krausApply A) =
      (liouville (krausApply A)).trace.re / 4 ∧
    QuditFidelity.entanglementFidelity 2 (by decide) (krausApply A) =
      effectProb (pureDensity (finiteMaxEntangled (Fin 2))) ((1 / 2 : ℂ) • outputFirstChoi (krausApply A)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
