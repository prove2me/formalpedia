-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P37_one_atom_exact
-- name    : QAlgorithms.Papers.Independent.Intake100.P37.one_atom_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:02:48.079664+00:00
-- url     : https://prove2.me/theorems/31fda9e3-de55-41df-b687-9def020872d2
-- title:
--   One atom: exact dynamics, success probability, and Buzek-Hillery identification
-- statement:
--   For one Lambda atom and one incident photon in polarization 1, define $F_0=|e\rangle|1,0\rangle$ and the original-atomic-convention vector
--
--   $$
--   F_1=\sqrt{\frac23}|g_1\rangle|2,0\rangle+\sqrt{\frac13}|g_2\rangle|1,1\rangle.
--   $$
--
--   For every real coupling $\gamma$ and time $t$, $F_1$ is normalized and the full physical evolution is
--
--   $$
--   e^{-itH}F_0=\cos(\gamma\sqrt3t)F_0-i\sin(\gamma\sqrt3t)F_1,
--   \qquad p(1)=\sin^2(\gamma\sqrt3t).
--   $$
--
--   The constructed physical sector agrees with $F_1$ and its relative-frequency fidelity is $5/6$. The explicit readout $|2,0\rangle\mapsto|11\rangle$, $|1,1\rangle\mapsto(|01\rangle+|10\rangle)/\sqrt2$, $g_1\mapsto\downarrow$, $g_2\mapsto\uparrow$ sends $F_1$ to the Buzek-Hillery state (8), with the printed positive branch amplitudes. This identifies the full output, beyond its fidelity alone.
-- source:
--   Lambda's, V's and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, PDF p. 3, Sec. II A, Eqs.(4)-(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P37

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3 Eqs.(4)-(8): exact one-atom full vector with its -i phase,
cloning probability, 5/6 fidelity, and the explicit BH three-qubit identification. -/
theorem one_atom_exact (gamma t : ℝ) :
    IsState oneAtomKet ∧
    physicalOutput 1 1 gamma t (ket (0 : Fin 2)) =
      (Real.cos (gamma * Real.sqrt 3 * t) : ℂ) • physicalInput 1 1 (ket (0 : Fin 2)) +
      (-Complex.I * (Real.sin (gamma * Real.sqrt 3 * t) : ℂ)) • oneAtomKet ∧
    excitedOutcomeProbability 1 1 1 gamma t (ket (0 : Fin 2)) = Real.sin (gamma * Real.sqrt 3 * t) ^ 2 ∧
    physicalSector 1 1 1 (ket (0 : Fin 2)) = oneAtomKet ∧
    sectorFidelity 1 1 1 = 5 / 6 ∧
    applyMatrix bhReadout oneAtomKet = bhKet := by sorry

end QAlgorithms.Papers.Independent.Intake100.P37

end
