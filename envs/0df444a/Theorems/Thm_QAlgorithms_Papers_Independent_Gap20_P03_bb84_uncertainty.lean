-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_bb84_uncertainty
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.bb84_uncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:16:13.486218+00:00
-- url     : https://prove2.me/theorems/d5db7949-5f47-4eec-9882-6a0253e58642
-- title:
--   Corollary 3.4: BB84 uncertainty
-- statement:
--   Let $\rho$ be any density state on $n\ge0$ qubits. Measure each qubit in a fresh independent uniform basis from the computational and Hadamard bases; let $\Theta$ record the bases and $X$ the outcomes. For $0<\lambda<1/2$,
--   $$H_\infty^\varepsilon(X\mid\Theta)\ge(1/2-2\lambda)n,\qquad\varepsilon=\exp\!\left(-\frac{\lambda^2n}{32[2-\log_2\lambda]^2}\right).$$
--   The entropy uses classical worst-case conditioning and event-deletion smoothing. This is the BB84 specialization of the general uncertainty relation.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 8, Corollary 3.4: BB84 uncertainty

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Corollary 3.4, p.8: fresh independent BB84 bases on any n-qubit state. -/
theorem bb84_uncertainty (n : ℕ) (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (lambda : ℝ) (hlambda : 0 < lambda)
    (hlambdaHalf : lambda < 1/2) :
    ((((1/2:ℝ)-2*lambda)*n : ℝ) : EReal) ≤
      smoothMin (measurementExperiment bb84Basis rho) Prod.fst Prod.snd
        (bb84Error n lambda) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
