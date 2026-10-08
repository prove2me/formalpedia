-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_lemma_3_12
-- name    : SelfScaledIPM.FuncProx.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:03.980489+00:00
-- url     : https://prove2.me/theorems/9692f18b-6f3b-48a4-866e-75a6a586753d
-- title:
--   Lemma 3.12, pp. 12–13 — with w̄ = √µ w, x̄ = x/√µ: 2(F(x) − F(w̄)) = γ_F ≥ 0, ≥ ‖x̄ − w‖²_w = ‖w̄ − x‖²_w̄, ≤ γ_G − ‖w̄ − x‖²_x
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, let $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$ with scaling point $w$, let $\mu=\mu(x,s)=\langle s,x\rangle/\nu$, and put $\bar w=\sqrt{\mu}\,w$, $\bar x=x/\sqrt{\mu}$. Then
--   $$2(F(x)-F(\bar w))=F(x)+F_*(s)+\nu\ln\mu+\nu\ \ge 0, \tag{3.19}$$
--   $$2[F(x)-F(\bar w)]\ge\|\bar x-w\|_w^2=\|\bar w-x\|_{\bar w}^2, \tag{3.20}$$
--   $$2[F(x)-F(\bar w)]\le[\mu\langle F'(x),F_*'(s)\rangle-\nu]-\|\bar w-x\|_x^2. \tag{3.21}$$
--   The middle expression of (3.19) is $\gamma_F(x,s)$ and the bracket in (3.21) is $\gamma_G(x,s)$.
--
--   The lemma expresses the functional proximity measure as a barrier difference between $x$ and the scaled scaling point, and bounds it by distances; it underlies the estimates of Lemma 5.4.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), pp. 12–13, Lemma 3.12, (3.19)–(3.21)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Lemma 3.12** (pp. 12–13). For `x ∈ int K`, `s ∈ int K*` with scaling point `w`, let
`µ = µ(x, s)`, `w̄ = √µ w`, `x̄ = x/√µ`. Then
(3.19) `2(F(x) − F(w̄)) = γ_F(x, s) ≥ 0` (`γ_F` is the page's middle expression
`F(x) + F*(s) + ν ln µ + ν`);
(3.20) `2[F(x) − F(w̄)] ≥ ‖x̄ − w‖²_w = ‖w̄ − x‖²_{w̄}`;
(3.21) `2[F(x) − F(w̄)] ≤ γ_G(x, s) − ‖w̄ − x‖²_x`. -/
theorem lemma_3_12
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K))
    (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w) :
    (2 * (F x - F (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w)) = gammaF K F ν x s ∧
      0 ≤ 2 * (F x - F (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w))) ∧
    (SelfScaledIPM.ShortStep.lnorm F w ((Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s))⁻¹ • x - w) ^ 2 ≤
        2 * (F x - F (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w)) ∧
      SelfScaledIPM.ShortStep.lnorm F w ((Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s))⁻¹ • x - w) ^ 2 =
        SelfScaledIPM.ShortStep.lnorm F (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w) (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w - x) ^ 2) ∧
    2 * (F x - F (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w)) ≤
      gammaG K F ν x s - SelfScaledIPM.ShortStep.lnorm F x (Real.sqrt (SelfScaledIPM.ShortStep.mu ν x s) • w - x) ^ 2 := by sorry

end SelfScaledIPM.FuncProx
