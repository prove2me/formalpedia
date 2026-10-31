-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_bsa_entanglement_well_defined
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.bsa_entanglement_well_defined
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:27:08.49971+00:00
-- url     : https://prove2.me/theorems/b680d087-4053-4567-abd8-1edf714c4a3b
-- title:
--   The BSA entanglement functional is unambiguous
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^2\otimes\mathbb C^2$, and let $\lambda(\rho)$ be the optimal separable trace. Write $S_*(\rho)$ for any selected unrestricted BSA, $R_*=\rho-S_*$, and $w_*=\operatorname{Tr}R_*$. Define $E_{\mathrm{BSA}}(\rho)=0$ when $w_*=0$, and otherwise define it by $w_*S_2(\operatorname{Tr}_B(R_*/w_*))$, where $S_2(\tau)=-\operatorname{Tr}(\tau\log_2\tau)$, with $0\log_2 0=0$. The selected operator is an actual optimizer. For every unrestricted optimizer $S$, a zero residual gives $E_{\mathrm{BSA}}(\rho)=0$; for every unit vector $\psi$ and real $w>0$ with $\rho-S=w|\psi\rangle\langle\psi|$,
--
--   $$w=1-\lambda(\rho),\qquad E_{\mathrm{BSA}}(\rho)=wS_2\!\left(\operatorname{Tr}_B|\psi\rangle\langle\psi|\right)=wS_2\!\left(\operatorname{Tr}_A|\psi\rangle\langle\psi|\right).$$
--
--   Thus the value is independent of the optimizer selection, vector representative, and choice of reduced subsystem. This is the functional introduced in the paper; no assertion about a different mixed-state entanglement measure is included.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 3, Eqs. (12)-(13): unambiguous BSA entanglement functional

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.3, Eqs. (12)–(13): the defined functional agrees with the weighted
pure residual entropy for every optimal decomposition and either subsystem;
it is zero at a vanishing residual. This asserts representative independence,
not entanglement of formation or an LOCC monotonicity property. -/
theorem bsa_entanglement_well_defined
    (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hrho : IsDensityMatrix rho) :
    IsBSA rho (bsaRepresentative rho) ∧
      ∀ S, IsBSA rho S →
        (rho - S = 0 → bsaEntanglement rho = 0) ∧
        ∀ (psi : EuclideanSpace ℂ (Fin 2 × Fin 2)) (w : ℝ),
          IsState psi → 0 < w → rho - S = (w : ℂ) • pureDensity psi →
            w = 1 - bsaWeight rho ∧
            bsaEntanglement rho = w * vnEntropy (traceRight (pureDensity psi)) ∧
            bsaEntanglement rho = w * vnEntropy (traceLeft (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
