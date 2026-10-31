-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_4_15
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_4_15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:26:33.090266+00:00
-- url     : https://prove2.me/theorems/b4ff5b17-9b85-4e4f-b788-b6940f9166db
-- title:
--   Theorem 4.15
-- statement:
--   For $0<\psi<\pi$, let $\mathcal R_H(\Sigma_\psi)$ be the $\mathcal H_\psi$ closure of the resolvent span with $\lambda\in\Sigma_{\pi-\psi}$. Then
--
--   $$\mathcal R_H(\Sigma_\psi)=\{f\in\mathcal H_\psi:f(\infty)=0\}.$$
--
--   Thus rational approximation characterizes the vanishing ideal of the sector algebra.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 23, Theorem 4.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 4.15, arXiv:2202.03143v1, PDF page(s) 23, 24. -/
theorem theorem_4_15
(psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi) (f : AnalyticSymbol) (hf : HardySobolevClass psi f) :
    NormClosure (ResolventSpan (openSectorDomain psi) (openSectorDomain (Real.pi - psi)) false)
      (hSize psi) f ↔ infinityValue f = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
