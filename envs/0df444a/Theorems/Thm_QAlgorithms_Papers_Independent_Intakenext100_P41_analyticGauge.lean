-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_analyticGauge
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.analyticGauge
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:31:59.258015+00:00
-- url     : https://prove2.me/theorems/4e85473d-6b04-44e5-bcab-c208d8dcc69c
-- title:
--   Unique normalized holomorphic regular-singular gauge
-- statement:
--   Let $d\ge1$, $m\ge0$, $R>0$, and let $B(t,z)$ be a jointly holomorphic $d\times d$ matrix family on $\mathbb C^m\times\{|z|<R\}$. Set $A(t,z)=B(t,z)/z$ for $z\ne0$ and $A_0(t)=B(t,0)$. Let $U$ consist of the parameters at which no two eigenvalues of $A_0(t)$ differ by a positive integer. There exists a holomorphic invertible matrix family $g$ on $U\times\{|z|<R\}$, uniquely determined there by $g(t,0)=I$ and
--
--   $$g(t,z)^{-1}A(t,z)g(t,z)-g(t,z)^{-1}\frac{\partial g}{\partial z}(t,z)=\frac{A_0(t)}{z}\qquad(0<|z|<R).$$
--
--   The source proof explicitly imposes $g_0(t)=I$, omitted from the printed uniqueness statement. The holomorphic family $B=zA$ encodes the locally normally convergent Laurent family; uniqueness concerns values on the stated domain.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 26, §19: Proposition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §19 proposition, PDF p.26, with g(t,0)=I restored from the proof's g₀(t)=I.
The printed uniqueness claim omits that normalization and is false without it.
B=zA is jointly holomorphic, encoding the locally normally convergent Laurent
family. Uniqueness is on U×{|z|<R}, not on arbitrary outside values. -/
theorem analyticGauge (d m : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (B : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ)
    (hB : DifferentiableOn ℂ B (Set.univ ×ˢ Metric.ball (0 : ℂ) R)) :
    ∃ g : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ,
      IsNormalizedGauge R B g ∧
      ∀ h : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ,
        IsNormalizedGauge R B h → Set.EqOn h g (gaugeDomain R B) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
