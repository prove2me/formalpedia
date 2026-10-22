-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_sixState_uncertainty
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.sixState_uncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:17:50.557311+00:00
-- url     : https://prove2.me/theorems/e7e96f0b-0f46-45d7-96ec-32a8a55d7e48
-- title:
--   Unnumbered: six-state uncertainty corollary
-- statement:
--   Let $\rho$ be any density state on $n\ge0$ qubits. Independently choose each measurement basis uniformly from the computational, Hadamard, and circular bases, whose circular vectors are $(|0\rangle\pm i|1\rangle)/\sqrt2$. Write $\Theta$ for these bases and $X$ for the outcomes. For $0<\lambda<1/2$,
--   $$H_\infty^\varepsilon(X\mid\Theta)\ge(2/3-2\lambda)n,\qquad\varepsilon=\exp\!\left(-\frac{\lambda^2n}{32[\log_2(6/\lambda)]^2}\right).$$
--   This is the six-state corollary obtained from the average uncertainty bound $2/3$ cited to Sánchez-Ruiz. No equality for arbitrary states is claimed.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 8, Unnumbered: six-state uncertainty corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Section 3, p.8, six-state corollary: d=2, |B|=3, h=2/3. -/
theorem sixState_uncertainty (n : ℕ) (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (lambda : ℝ) (hlambda : 0 < lambda)
    (hlambdaHalf : lambda < 1/2) :
    ((((2/3:ℝ)-2*lambda)*n : ℝ) : EReal) ≤
      smoothMin (measurementExperiment sixBasis rho) Prod.fst Prod.snd
        (accumulationError 6 n lambda) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
