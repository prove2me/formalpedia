-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_13
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:25:34.590413+00:00
-- url     : https://prove2.me/theorems/4e5ba203-fe5c-40cf-a00d-85ea17481cf7
-- title:
--   Proposition 4.13
-- statement:
--   For $f\in\mathcal H_\psi$, put $\gamma=\pi/(2\psi)$ and $f_\psi(t)=(f(te^{i\psi})+f(te^{-i\psi}))/2$, using continuous boundary values. For $z\in\Sigma_\psi\cup\{0\}$,
--
--   $$f(z)=f(\infty)-\frac2\pi\int_0^\infty f_\psi'(t)\operatorname{arccot}(z^\gamma/t^\gamma)\,dt.$$
--
--   The boundary derivative has its almost-everywhere absolutely continuous interpretation. This is the line-integral reproducing formula.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 23, Proposition 4.13

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.13, arXiv:2202.03143v1, PDF page(s) 23. -/
theorem proposition_4_13
(psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi) (f : AnalyticSymbol) (hf : HardySobolevClass psi f) :
    let gamma := Real.pi / (2 * psi)
    ∀ z : ℂ, z ∈ openSectorDomain psi ∨ z = 0 →
      Integrable (fun t : ℝ => deriv (boundaryAverage psi f) t *
        arccotZero (z ^ (gamma : ℂ) / (t : ℂ) ^ (gamma : ℂ))) positiveVolume ∧
      extension (openSectorDomain psi) f z = infinityValue f - (2 / (Real.pi : ℂ)) *
        ∫ t, deriv (boundaryAverage psi f) t *
          arccotZero (z ^ (gamma : ℂ) / (t : ℂ) ^ (gamma : ℂ)) ∂positiveVolume := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
