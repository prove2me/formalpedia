-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_7
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:22:51.855358+00:00
-- url     : https://prove2.me/theorems/11b3321c-f6d2-414d-a4d2-df1b5afdd6f7
-- title:
--   Proposition 4.7
-- statement:
--   Let $0<\psi<\pi$ and $f\in\mathcal H_\psi$. The function extends continuously and boundedly to the closed sector and has a finite limit at infinity throughout that sector. Its continuous values satisfy
--
--   $$|f(z)|\le |f(\infty)|+\|f'\|_{H^1(\Sigma_\psi)}\qquad(z\in\overline{\Sigma_\psi}).$$
--
--   This gives the canonical boundary values and norm for the Hardy-Sobolev algebra.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 21, Proposition 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.7, arXiv:2202.03143v1, PDF page(s) 21. Source correction: printed clause 3 says z in C_+, although f may be defined only on a narrower sector. Changed to the native sector and its continuous boundary, as required by the preceding power-transport argument. Independent moderation is pending. -/
theorem proposition_4_7
(psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi) (f : AnalyticSymbol) (hf : HardySobolevClass psi f) :
    EqOn (extension (openSectorDomain psi) f) f (openSectorDomain psi) ∧
    ContinuousOn (extension (openSectorDomain psi) f) (closure (openSectorDomain psi)) ∧
    supSize (closure (openSectorDomain psi)) (extension (openSectorDomain psi) f) < ⊤ ∧
    Tendsto f (infinityWithin (openSectorDomain psi)) (𝓝 (infinityValue f)) ∧
    ∀ z ∈ closure (openSectorDomain psi),
      ENNReal.ofReal ‖extension (openSectorDomain psi) f z‖ ≤
        ENNReal.ofReal ‖infinityValue f‖ + hardySize psi (deriv f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
