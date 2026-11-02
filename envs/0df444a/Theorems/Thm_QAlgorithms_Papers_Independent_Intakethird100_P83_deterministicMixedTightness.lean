-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_deterministicMixedTightness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.deterministicMixedTightness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:20:11.68721+00:00
-- url     : https://prove2.me/theorems/62428097-ec97-40ba-989b-843a27a3a1b3
-- title:
--   Mixed-state tightness and failure of the support-projector choice
-- statement:
--   Let $\rho^{(1/2)}$ be the equal mixture of the three normalized qutrit vectors $(|01\rangle+|10\rangle)/\sqrt2$, $(|02\rangle+|20\rangle)/\sqrt2$, and $(|12\rangle+|21\rangle)/\sqrt2$. Let $P$ be its support projector. With $E_1$ the one-copy exact positive-real-target PPT rate and $E_{\Gamma,0}$ its regularization, one has
--
--   $$E_1(\rho^{(1/2)})=E_{\Gamma,0}(\rho^{(1/2)})=E_\Gamma(\rho^{(1/2)})=E_W(\rho^{(1/2)})=\log_2(3/2)<\log_2(5/3)=E_N(\rho^{(1/2)}).$$
--
--   Moreover, $\|T_B(P)\|_\infty=1$, so the projector lower bound is $-\log_2\|T_B(P)\|_\infty=0<E_1(\rho^{(1/2)})$. This genuinely mixed example makes the first three comparison inequalities equalities. LOCC achievability remains open in the source.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 5, Unnumbered result: mixed-state coincidence and failure of the projector choice

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

/-- Mixed-state coincidence and failure of the R=P choice, PDF p.5,
with values from Proposition 5 on p.4. No LOCC achievability is asserted. -/
theorem deterministicMixedTightness :
    oneCopyExact (rhoAlpha (1/2)) = Real.logb 2 (3/2) ∧
    exactRegularized (rhoAlpha (1/2)) = Real.logb 2 (3/2) ∧
    entanglementGamma (rhoAlpha (1/2)) = Real.logb 2 (3/2) ∧
    entanglementW (rhoAlpha (1/2)) = Real.logb 2 (3/2) ∧
    entanglementN (rhoAlpha (1/2)) = Real.logb 2 (5/3) ∧
    Real.logb 2 (3/2) < Real.logb 2 (5/3) ∧
    complexSpectralNorm (partialTranspose (supportProjector (rhoAlpha (1/2)))) = 1 ∧
    -Real.logb 2 (complexSpectralNorm (partialTranspose (supportProjector (rhoAlpha (1/2))))) = 0 ∧
    0 < oneCopyExact (rhoAlpha (1/2)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
