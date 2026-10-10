-- Prove2me | Theorems.Thm_UhlenbeckGauge_trWedge_curvature_eq_div_chernSimons
-- name    : UhlenbeckGauge.trWedge_curvature_eq_div_chernSimons
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:37.186984+00:00
-- url     : https://prove2.me/theorems/6f8d127a-5279-42e1-af64-cfb5a48cca04
-- title:
--   Fact 3.1.3 (local form) — $\operatorname{tr}(F_A\wedge F_A)=d\,CS(A)$
-- statement:
--   Let $A$ be a smooth $SU(n)$-connection on the trivial bundle over $\mathbb R^4$, with curvature $F_A$, and let $K^\mu(A)=\sum_{\nu,\rho,\sigma}\varepsilon_{\mu\nu\rho\sigma}\operatorname{tr}(A_\nu\partial_\rho A_\sigma+\tfrac23A_\nu A_\rho A_\sigma)$ be the components of the Chern–Simons three-form $CS(A)=\operatorname{tr}(A\wedge dA+\tfrac23A\wedge A\wedge A)$. Then at every point $x\in\mathbb R^4$
--   $$\operatorname{tr}(F_A\wedge F_A)(x)=\sum_{\mu=0}^{3}\partial_\mu K^\mu(A)(x),$$
--   that is, $\operatorname{tr}(F_A\wedge F_A)=d\,CS(A)$. This is the local identity that makes $\operatorname{tr}(F_A\wedge F_A)$ a "topological term" which integrates to a boundary contribution.
--
--   **Formalization Note** The Chern–Simons form uses the standard coefficient $\tfrac23$ (equivalently $\operatorname{tr}(A\wedge F_A)-\tfrac13\operatorname{tr}(A\wedge A\wedge A)$); the $\tfrac16$ printed on p. 32 of the notes does not satisfy $d\,CS=\operatorname{tr}(F\wedge F)$ with $F_A=dA+A\wedge A$.
-- source:
--   K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, discussion of Fact 3.1.3 and the Chern-Simons three-form (p. 32)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem trWedge_curvature_eq_div_chernSimons {n : ℕ} (A : Connection n)
    (hA : IsSUConnection A) (x : R4) :
    trWedge (curvature A x) =
      ∑ μ : Fin 4, fderiv ℝ (chernSimonsCurrent A μ) x (Pi.single μ 1) := by sorry

end UhlenbeckGauge
