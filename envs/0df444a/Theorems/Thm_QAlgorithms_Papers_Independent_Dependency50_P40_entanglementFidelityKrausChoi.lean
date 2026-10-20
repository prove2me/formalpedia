-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_entanglementFidelityKrausChoi
-- name    : QAlgorithms.Papers.Independent.Dependency50.P40.entanglementFidelityKrausChoi
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:20:16.772085+00:00
-- url     : https://prove2.me/theorems/783e7c18-6db6-495f-882e-3751d4c57655
-- title:
--   General-input entanglement fidelity in Kraus and Choi forms
-- statement:
--   Let $H=\mathbb C^h$, $h>0$, let $\rho\succeq0$ have trace one, and let $|\psi\rangle\in A\otimes H$ be any unit purification with $\operatorname{tr}_A|\psi\rangle\langle\psi|=\rho$, where $A$ is finite. For a CPTP channel $\mathcal B(M)=\sum_iB_iMB_i^\dagger$, define $F_e$ by the purification expression (6) and $X_B=\sum_i|B_i\rangle\rangle\langle\langle B_i|$. Then
--
--   $$
--   F_e(\rho,\mathcal B)
--   =\sum_i|\operatorname{tr}(\rho B_i)|^2
--   =\sum_i\langle\langle\rho|B_i\rangle\rangle\langle\langle B_i|\rho\rangle\rangle
--   =\langle\langle\rho|X_B|\rho\rangle\rangle.
--   $$
--
--   Inner products conjugate the first argument. The operator ket $|\rho\rangle\rangle$ has squared norm $\operatorname{tr}\rho^2$, and is not normalized separately. These identities turn the purification definition into an algebraic linear objective; (16) is standard background attributed to [12].
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, PDF p. 3, IV, Eqs. (16)-(17): general-input entanglement fidelity in Kraus and Choi form

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF pp.2–3, (6), (16)–(17): general-input entanglement fidelity.
The Kraus identity is standard background attributed to Schumacher [12]. -/
theorem entanglementFidelityKrausChoi {h a m : ℕ} (hh : 0 < h)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (B : Fin m → Matrix (Fin h) (Fin h) ℂ) (hB : IsKrausFamily B) :
    purificationFidelity psi (krausApply B) = ∑ i, Complex.normSq ((rho * B i).trace) ∧
    purificationFidelity psi (krausApply B) =
      (∑ i, (inner ℂ (operatorKet rho) (operatorKet (B i))) *
        (inner ℂ (operatorKet (B i)) (operatorKet rho))).re ∧
    purificationFidelity psi (krausApply B) = (complexQuadraticForm (operatorKet rho) (krausChoi B)).re := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P40

end
