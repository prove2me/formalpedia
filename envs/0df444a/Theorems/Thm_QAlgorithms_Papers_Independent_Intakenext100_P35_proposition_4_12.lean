-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_12
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:24:58.228725+00:00
-- url     : https://prove2.me/theorems/a98a65cc-fffe-43cc-8168-80cd9734db7d
-- title:
--   Proposition 4.12
-- statement:
--   Let $f\in\mathcal H_\psi$, $0<\psi<\pi$, put $\nu=2\psi/\pi$, and write $f_\nu(w)=f(w^\nu)$. For $z\in\Sigma_\psi\cup\{0\}$,
--
--   $$f(z)=f(\infty)-\frac1\pi\int_0^\infty\int_{\mathbb R}\frac{f_\nu'(\alpha+i\beta)}{\alpha-i\beta+z^{1/\nu}}\,d\beta\,d\alpha.$$
--
--   The value at zero is the continuous sectorial limit. This gives an area-integral representation on a sector.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 22, Proposition 4.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.12, arXiv:2202.03143v1, PDF page(s) 22. -/
theorem proposition_4_12
(psi : ℝ) (hpsi : 0 < psi) (hpi : psi < Real.pi) (f : AnalyticSymbol) (hf : HardySobolevClass psi f) :
    let nu := 2 * psi / Real.pi
    ∀ z : ℂ, z ∈ openSectorDomain psi ∨ z = 0 →
      AbsoluteDouble (fun a b => deriv (powerPull nu f) (point a b) /
        (point a (-b) + z ^ ((1 / nu : ℝ) : ℂ))) ∧
      extension (openSectorDomain psi) f z = infinityValue f - (1 / (Real.pi : ℂ)) *
        ∫ a, ∫ b, deriv (powerPull nu f) (point a b) /
          (point a (-b) + z ^ ((1 / nu : ℝ) : ℂ)) ∂volume ∂positiveVolume := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
