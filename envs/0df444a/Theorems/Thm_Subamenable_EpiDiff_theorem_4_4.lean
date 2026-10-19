-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_theorem_4_4
-- name    : Subamenable.EpiDiff.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:38.722981+00:00
-- url     : https://prove2.me/theorems/d4e6e511-a34c-494b-a8af-6496d11a4318
-- title:
--   Theorem 4.4 — critical cone is the domain of the second subderivative
-- statement:
--   Let $\varphi$ be fully subamenable at $\bar x$, represented locally by $\vartheta\circ f$, and set $\Omega=\{x:f(x)\in\operatorname{dom}\vartheta\}$. Then its limiting and proximal subdifferentials at $\bar x$ agree. For each $w\in T_\Omega(\bar x)$, the first subderivative $d\varphi(\bar x)(w)$ is finite and the epigraph has a second-order tangent vector above $(w,d\varphi(\bar x)(w))$. Consequently, for every $\bar v\in\partial\varphi(\bar x)$,
--
--   $$K_\varphi(\bar x,\bar v)=\operatorname{dom}d^2\varphi(\bar x,\bar v).$$
--
--   The theorem connects feasible tangent geometry to the directions with finite second subderivative.
--
--   **Formalization Note** The source's epigraph tangent uses a real second coordinate; finiteness of $d\varphi(\bar x)(w)$ is stated explicitly instead of converting an infinite value to a real default.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, pp. 17–19, Theorem 4.4, (4.5)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

namespace Subamenable.EpiDiff

theorem theorem_4_4 {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar) :
    NonconvexSplitting.Shared.LimitingSubdiff phi xbar = proxSubdiff phi xbar ∧
    (∀ w ∈ tangentCone (f ⁻¹' dom theta) xbar,
      ∃ c : ℝ, subderiv phi xbar w = (c : EReal) ∧
        (secondTangentSet
          {p : E n × ℝ | phi p.1 ≤ (p.2 : EReal)}
          (xbar, (phi xbar).toReal) (w, c)).Nonempty) ∧
    ∀ vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff phi xbar,
      criticalCone phi xbar vbar = dom (secondSubderiv phi xbar vbar) := by sorry

end Subamenable.EpiDiff
