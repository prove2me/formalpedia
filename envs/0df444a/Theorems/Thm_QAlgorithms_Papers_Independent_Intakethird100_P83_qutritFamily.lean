-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_qutritFamily
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.qutritFamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:13:11.732201+00:00
-- url     : https://prove2.me/theorems/03ce5c96-fbb8-4bdf-ba8a-3eb73ebec28d
-- title:
--   Strict qutrit mixed-state family and an exact value
-- statement:
--   For $0<\alpha\le\tfrac12$, define the qutrit state $\rho^{(\alpha)}=\tfrac13\sum_{m=0}^2|\psi_m\rangle\langle\psi_m|$, where $\psi_0=\sqrt\alpha|01\rangle+\sqrt{1-\alpha}|10\rangle$, $\psi_1=\sqrt\alpha|02\rangle+\sqrt{1-\alpha}|20\rangle$, and $\psi_2=\sqrt\alpha|12\rangle+\sqrt{1-\alpha}|21\rangle$. These are normalized states, and the PPT distillable rate $E_\Gamma$, SDP measure $E_W$, and logarithmic negativity $E_N$ satisfy
--
--   $$E_\Gamma(\rho^{(\alpha)})\le E_W(\rho^{(\alpha)})\le\log_2\bigl(1+\sqrt{\alpha(1-\alpha)}\bigr)<E_N(\rho^{(\alpha)})=\log_2\bigl(1+\tfrac43\sqrt{\alpha(1-\alpha)}\bigr).$$
--
--   In particular,
--
--   $$E_\Gamma(\rho^{(1/2)})=E_W(\rho^{(1/2)})=\log_2(3/2)<\log_2(5/3)=E_N(\rho^{(1/2)}).$$
--
--   This gives a strict improvement on the negativity bound. The upper bound for general $\alpha$ is not asserted to be attained.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 4, Proposition 5: strict mixed-state family and an exact value

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Proposition 5 and its explicit bounds (11)–(12), PDF p.4.
The bound (12) is not asserted to be an equality for general alpha. -/
theorem qutritFamily (alpha : ℝ) (hpos : 0 < alpha) (hhalf : alpha ≤ 1/2) :
    IsDensityMatrix (rhoAlpha alpha) ∧
    entanglementGamma (rhoAlpha alpha) ≤ entanglementW (rhoAlpha alpha) ∧
    entanglementW (rhoAlpha alpha) ≤ Real.logb 2 (1 + Real.sqrt (alpha * (1-alpha))) ∧
    entanglementN (rhoAlpha alpha) = Real.logb 2 (1 + (4/3 : ℝ) * Real.sqrt (alpha * (1-alpha))) ∧
    entanglementW (rhoAlpha alpha) < entanglementN (rhoAlpha alpha) ∧
    entanglementGamma (rhoAlpha (1/2)) = Real.logb 2 (3/2) ∧
    entanglementW (rhoAlpha (1/2)) = Real.logb 2 (3/2) ∧
    entanglementN (rhoAlpha (1/2)) = Real.logb 2 (5/3) ∧
    Real.logb 2 (3/2) < Real.logb 2 (5/3) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
