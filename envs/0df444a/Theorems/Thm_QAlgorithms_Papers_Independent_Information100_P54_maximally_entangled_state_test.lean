-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P54_maximally_entangled_state_test
-- name    : QAlgorithms.Papers.Independent.Information100.P54.maximally_entangled_state_test
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:10:18.252607+00:00
-- url     : https://prove2.me/theorems/9670cd51-b7d5-4952-8efb-477774b84a52
-- title:
--   Lemma 8 (Maximally entangled-state test)
-- statement:
--   Let $d\ge1$ be finite, let $\rho$ be a normalized state on two registers of local dimension $d$, and let $0\le\varepsilon<1$. Write $\Phi_d=d^{-1}\sum_{i,j=0}^{d-1}|ii\rangle\langle jj|$ for the maximally entangled projector, and $h_2(u)=-u\log_2u-(1-u)\log_2(1-u)$. If $\operatorname{Tr}(\Phi_d\rho)\ge1-\varepsilon$, then
--
--   $$E_R^\infty(\rho)\ge(1-\varepsilon)\log_2d-h_2(\varepsilon).$$
--
--   Here $E_R(\rho)=\inf_{\sigma\in\mathrm{SEP}}D(\rho\Vert\sigma)$ and $E_R^\infty(\rho)=\lim_{r\to\infty}E_R(\rho^{\otimes r})/r$, with all logarithms base two. Regularization uses independent copies of this fixed state and the aggregate Alice–Bob cut. This tests regularized entanglement rather than only one-copy REE.
-- source:
--   Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels, arXiv:2610.06832v1, PDF p. 18, Lemma 8 (Maximally entangled-state test)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section

open scoped ENNReal Matrix

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P54

/-- arXiv:2610.06832v1, PDF pp.18–19, Lemma 8, Eq.(C5).
Every tensor power uses the aggregate Alice:Bob cut. Lifting the real lower bound
to ENNReal is equivalent because REE is nonnegative. -/
theorem maximally_entangled_state_test (d : ℕ) (hd : 1 ≤ d)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    (hfidelity : 1 - eps ≤ ((maximallyEntangledProjector d * rho).trace.re)) :
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    ENNReal.ofReal ((1 - eps) * (Real.log d / Real.log 2) - QAlgorithms.binEntropy2 eps) ≤
      regularizedEntanglement rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P54

end
