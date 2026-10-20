-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_directionalExampleFiniteTO
-- name    : QAlgorithms.Papers.Independent.Information100.P44.directionalExampleFiniteTO
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:48:06.875793+00:00
-- url     : https://prove2.me/theorems/8868e4ca-a289-473b-9a44-c31dca5a54a9
-- title:
--   Remark 11: the directional counterexample is a finite thermal operation
-- statement:
--   Let $H=\operatorname{diag}(E_0,E_1,E_1)$ with $E_0\ne E_1$, $q\in(0,1)$, and finite $\beta>0$. For $\Phi_q(X)=qX+(1-q)U_-XU_-^\dagger$, $U_-=\operatorname{diag}(1,1,-1)$, choose a bath qubit with energies $0,\epsilon_q$, where
--   $$\epsilon_q=\beta^{-1}\log\frac{q}{1-q}\quad(q\ge1/2),\qquad \epsilon_q=\beta^{-1}\log\frac{1-q}{q}\quad(q<1/2).$$
--   There is an energy-preserving bath-controlled unitary dilation realizing $\Phi_q$: use the identity on the ground control and $U_-$ on the excited control when $q\ge1/2$, and swap these controls when $q<1/2$. At $q=1/2$ the bath is degenerate. This gives an explicit finite thermal realization, rather than assuming one.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 20, Remark 11: the directional counterexample is a finite thermal operation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.20, Remark 11: an explicitly specified bath qubit and controlled unitary realize
Phi_q for every positive finite beta. The q=1/2 bath is degenerate. -/
theorem directionalExampleFiniteTO (E0 E1 beta q : ℝ) (hE : E0 ≠ E1)
    (hbeta : 0 < beta) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ D : ThermalDilation ![E0,E1,E1] beta 2,
      D.bathEnergy = ![0, mixtureBathGap beta q] ∧
      (D.U : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) = mixtureBathUnitary q ∧
      ∀ X, thermalApply D X = directionalMixture q X := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
