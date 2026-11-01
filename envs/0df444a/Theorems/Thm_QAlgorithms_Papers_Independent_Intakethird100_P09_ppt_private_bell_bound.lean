-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P09_ppt_private_bell_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P09.ppt_private_bell_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:39:21.978733+00:00
-- url     : https://prove2.me/theorems/fea6dad4-e0ea-4d31-8f3f-42a97a84a6d3
-- title:
--   Example Eqs. (9)–(10): explicit PPT approximate private states
-- statement:
--   All states are normalized finite-dimensional bipartite density matrices. Gamma denotes transposition of Bob in the fixed product basis. The trace norm is the full trace norm. For a finite Bell expression S with real coefficients, C(S) and Q(S) are its largest signed classical value and its supremal signed quantum value over arbitrary finite local dimensions; Q_S(rho) optimizes complete local POVMs on the fixed state. Let d>=1 and let U=(u_ij) be a d-dimensional unitary with |u_ij|=1/sqrt(d). Define
--
--   $$X=\frac1{d\sqrt d}\sum_{i,j}u_{ij}|ij\rangle\langle ji|,\quad Y=\sqrt d\,X^\Gamma,\quad p=\frac1{\sqrt d+1},$$
--
--   $$\rho_p=(1-p)\gamma_X+\frac p2\bigl(|01\rangle\langle01|\otimes\sqrt{YY^\dagger}+|10\rangle\langle10|\otimes\sqrt{Y^\dagger Y}\bigr).$$
--
--   Regroup the registers as AA′:BB′. The constructed rho_p is a density matrix and is PPT. For every nonnegative-coefficient Bell expression,
--
--   $$Q_S(\rho_p)\le C(S)+\frac{Q(S)}{\sqrt d}.$$
--
--   The printed flat modulus 1/d is corrected to 1/sqrt(d), as required by unitarity and the named Fourier example. Density and PPT are conclusions, not premises. This supplies explicit weakly nonlocal PPT approximate private bits.
--
--   The fixed private-bit formula used here is
--
--   $$\gamma_X=\frac12\left(|00\rangle\langle00|\otimes\sqrt{XX^\dagger}+|00\rangle\langle11|\otimes X+|11\rangle\langle00|\otimes X^\dagger+|11\rangle\langle11|\otimes\sqrt{X^\dagger X}\right),$$
--
--   with the two key qubits and shields regrouped by owner.
-- source:
--   Bounds on quantum nonlocality via partial transposition, arXiv:1407.6999v3, PDF p. 3, Example Eqs. (9)–(10): explicit PPT approximate private states

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms.Entanglement (IsSeparableDensity)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (transposeSecond partyCut xForm swapPrivate hidingOne hidingTwo)

open QAlgorithms.Papers.Independent.Dependency50.P42 (dimensionedPower)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Advance50.P47 (Box)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntanglement)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3, Eqs.(9)--(10): density and PPT are conclusions of the explicit construction.
CORRECTED flat modulus 1/sqrt(d), forced by unitarity; Bell domain corrected to s>=0. -/
theorem ppt_private_bell_bound (d : ℕ+) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (hflat : ∀ i j, ‖(U : Op (Fin d)) i j‖ = (Real.sqrt d)⁻¹) :
    IsDensityMatrix (pptPrivate d U) ∧ (transposeSecond (pptPrivate d U)).PosSemidef ∧
    ∀ (S : BellScenario) (s : BellCoefficients S), (∀ x y a b, 0 ≤ s x y a b) →
      stateValue s (pptPrivate d U) ≤ classicalBound s + quantumBound s / Real.sqrt d := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P09

end
