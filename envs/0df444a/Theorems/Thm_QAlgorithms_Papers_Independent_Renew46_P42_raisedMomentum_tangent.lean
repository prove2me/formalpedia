-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_raisedMomentum_tangent
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.raisedMomentum_tangent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:28:02.299935+00:00
-- url     : https://prove2.me/theorems/55eb22f0-b047-49a0-92f8-90bc4514d332
-- title:
--   Raised wave momentum is tangent to the ray
-- statement:
--   Let $c>0$, $n\ge1$, $|\mathbf u|<c$, and $\mathbf k\ne0$. Use $G=\eta+(n^2-1)UU^T$ and the massless Hamiltonian $H$ in (34). Raise the covector $p=(H/c,-\mathbf k)$ to obtain $K=Gp$. Then
--
--   $$K^0>0,\qquad \mathbf K=(K^0/c)\,\partial_{\mathbf k}H.$$
--
--   Separately, for $m>0$ and a future timelike tangent $v$ with $v^0>0$ and $g(v,v)>0$, construct $p=mc\,gv/\sqrt{g(v,v)}$. Its raised vector satisfies
--
--   $$K=\frac{mc}{\sqrt{g(v,v)}}v=\frac{K^0}{c}\frac{c}{v^0}v.$$
--
--   The last rescaling is the tangent in laboratory time $x^0/c$. The massless identity follows from its own Hamiltonian, without evaluating an undefined null proper-time quotient.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 6, §III D, (55)–(57): raised wave vector is tangent to a ray

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.6, (55)–(57): the raised covector is tangent, for massive tangents
and for the massless Hamiltonian branch separately. No null 0/0 is used. -/
theorem raisedMomentum_tangent (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    (let K := apply4 (gUp c n u) (waveCovector c (rayHamiltonian c n u k) k)
     0 < K 0 ∧ spatial K = (K 0 / c) • rayVelocity c n u k) ∧
    (∀ (m : ℝ) (v : V4), 0 < m → 0 < v 0 →
      0 < quadratic (gDown c n u) v →
      let K := apply4 (gUp c n u) (massiveCovector c m (gDown c n u) v)
      K = (m * c / Real.sqrt (quadratic (gDown c n u) v)) • v ∧
      K = (K 0 / c) • ((c / v 0) • v)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
