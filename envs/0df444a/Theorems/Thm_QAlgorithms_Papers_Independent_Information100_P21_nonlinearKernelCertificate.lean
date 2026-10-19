-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_nonlinearKernelCertificate
-- name    : QAlgorithms.Papers.Independent.Information100.P21.nonlinearKernelCertificate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:54:16.875929+00:00
-- url     : https://prove2.me/theorems/225096cb-5891-4d92-b1db-4b6092b1a115
-- title:
--   III.13 — Corollary III.13 (Nonlinear kernel certificate). In the nondegenerate case of Theorem III.12, the optimal vector and
-- statement:
--   For an entangled two-qubit state $\rho$ and a quotient maximizer $b_*$ with $\alpha_1>\alpha_2$, let $p=u_1\otimes f_1$ be its leading Schmidt product vector and $R$ the common robustness. Then
--   $$\rho^\Gamma b_*=-R\alpha_1p,\qquad\rho^\Gamma+R|p\rangle\langle p|\succeq0.$$
--   Conversely, let $\rho$ be a two-qubit state, $b$ a unit vector with Schmidt coefficients $\alpha_1>\alpha_2>0$, and $r>0$. If the same two equations hold with $b,r$, then $r=R_s(\rho)=R_g(\rho)$. The converse assumes no optimality; its physical noise is the projector onto $u_1\otimes\overline f_1$.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 12, III.13 — Corollary III.13 (Nonlinear kernel certificate). In the nondegenerate case of Theorem III.12, the optimal vector and

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 12, Corollary III.13 (Nonlinear kernel certificate). In the nondegenerate case of Theorem III.12, the optimal vector and. -/
theorem nonlinearKernelCertificate (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho)
  (b : Vec QQ) (hb : ‖b‖=1) (a1 a2 : ℝ) (u f : Fin 2 → Vec (Fin 2))
  (hs : schmidt b a1 a2 u f) (hne : a2<a1) :
  (¬sep rho → maximizer rho b →
    (pt rho).mulVec (fun i => b i) = fun i => ((-rg rho*a1:ℝ):ℂ) * tensor (u 0) (f 0) i) ∧
  (¬sep rho → maximizer rho b →
    (pt rho+(rg rho:ℂ) • proj (tensor (u 0) (f 0))).PosSemidef) ∧
  (∀ r : ℝ, 0<a2 → 0<r →
    (pt rho).mulVec (fun i => b i) = (fun i => ((-r*a1:ℝ):ℂ)*tensor (u 0) (f 0) i) →
    (pt rho+(r:ℂ) • proj (tensor (u 0) (f 0))).PosSemidef → r=rs rho ∧ r=rg rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
