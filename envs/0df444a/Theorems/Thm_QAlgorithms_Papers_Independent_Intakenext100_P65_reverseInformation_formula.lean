-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_reverseInformation_formula
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.reverseInformation_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:25:25.835977+00:00
-- url     : https://prove2.me/theorems/dc4a25e9-497b-40c4-9d8c-736e04effd87
-- title:
--   Closed formula for qubit reverse coherent information
-- statement:
--   Let $\mathcal E$ be any CPTP qubit channel. Form its output-first normalized Choi state $\rho_{\mathcal E}=(\mathcal E\otimes I)|\Psi\rangle\langle\Psi|$ and write $H$ for von Neumann entropy in bits. Set $D_{\mathcal E}=H(\operatorname{Tr}_{\rm ref}\rho_{\mathcal E})-H(\rho_{\mathcal E})$. For the Frobenius norm $\|A\|_F^2=\operatorname{Tr}(A^\dagger A)$, one has
--
--   $$D_{\mathcal E}=h_2\!\left(\frac12+\frac12\sqrt{\frac12\|\mathcal E(I)\|_F^2-1}\right)-H(\rho_{\mathcal E}).$$
--
--   Here $h_2(p)=-p\log_2p-(1-p)\log_2(1-p)$, with zero terms interpreted continuously. The marginal is $\mathcal E(I)/2$ on the output, not the unchanged reference marginal. This is an identity, without an optimization or capacity equality.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 7, §III (3.4): closed formula for the reverse coherent information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.7 (3.4): the output marginal eigenvalues have an external factor 1/2
and radicand (1/2)||E(I)||_F^2 - 1. -/
theorem reverseInformation_formula (T : Superop (Fin 2) (Fin 2)) (hT : IsChannel T) :
    reverseInformation T =
      binEntropy2 (1 / 2 + (1 / 2) * Real.sqrt ((1 / 2) * qubitFrobeniusSq (T 1) - 1)) -
        vnEntropy ((1 / 2 : ℂ) • outputFirstChoi T) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
