-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_localUnitaryInvariant
-- name    : QAlgorithms.Papers.Independent.Information100.P10.localUnitaryInvariant
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:38:15.305988+00:00
-- url     : https://prove2.me/theorems/dd3968cf-9ec6-4c5f-b2a7-5e72ed84d0d7
-- title:
--   Local-unitary and phase invariance: property ii
-- statement:
--   Let $\psi$ be a normalized $M$-qubit state, $\alpha\in\mathbb R$, and $U_\mu\in SU(2)$ independently on each wire. Put $\phi=e^{i\alpha}(\bigotimes_\mu U_\mu)\psi$, and let $r_\mu(\psi)$ denote the local Bloch vector. Then $\phi$ is normalized and
--
--   $$E(\phi)=E(\psi),\qquad \|r_\mu(\phi)\|_2^2=\|r_\mu(\psi)\|_2^2\quad\text{for every }\mu.$$
--
--   Consequently the geometric quantity is well defined on local-unitary orbits of physical pure-state rays.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 3, Local-unitary and phase invariance: property ii

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF pp.3-4, Eq.(11), property ii: invariance under local SU(2) and a global phase. -/
theorem localUnitaryInvariant {M : ℕ} (psi : Ket M) (hpsi : IsState psi)
    (alpha : ℝ) (U : Fin M → Matrix.specialUnitaryGroup Bool ℂ) :
    let phi := Complex.exp (Complex.I * (alpha : ℂ)) •
      act (kronAll (fun q => (U q : Matrix Bool Bool ℂ))) psi
    IsState phi ∧ entanglementDistance phi = entanglementDistance psi ∧
      ∀ q, ‖bloch phi q‖ ^ 2 = ‖bloch psi q‖ ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
