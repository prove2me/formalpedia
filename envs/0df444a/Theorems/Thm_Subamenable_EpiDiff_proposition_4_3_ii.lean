-- Prove2me | Theorems.Thm_Subamenable_EpiDiff_proposition_4_3_ii
-- name    : Subamenable.EpiDiff.proposition_4_3_ii
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-21T23:47:54.654959+00:00
-- url     : https://prove2.me/theorems/6d0b7f44-fe15-4991-9de6-8301918093be
-- title:
--   Proposition 4.3(ii) — chain rule for second-order tangent sets
-- statement:
--   Let $\varphi$ be fully subamenable at $\bar x$ through $\varphi=\vartheta\circ f$ ($\vartheta$ convex piecewise linear-quadratic, $f$ twice differentiable at $\bar x$, MSQC at $\bar x$), and set $\Omega=\{x: f(x)\in\operatorname{dom}\vartheta\}$. If $w\in T_\Omega(\bar x)$ and $z\in\mathbb R^n$ satisfy
--
--   $$\nabla f(\bar x)z+\nabla^2 f(\bar x)(w,w)\in T^2_{\operatorname{dom}\vartheta}\big(f(\bar x),\nabla f(\bar x)w\big),$$
--
--   then $z\in T^2_\Omega(\bar x,w)$. Furthermore, there exist $\varepsilon>0$ and an arc $\xi:[0,\varepsilon]\to\Omega$ with $\xi(0)=\bar x$, $\xi'_+(0)=w$ and $\xi''_+(0)=z$, where $\xi''_+(0)=\lim_{t\downarrow0}\big(\xi(t)-\xi(0)-t\xi'_+(0)\big)/(\tfrac12t^2)$.
--
--   **Formalization Note.** The arc is encoded by its defining second-order expansion: $\xi(t)\in\Omega$ for all small $t>0$ and $\frac{2}{t^2}\big(\xi(t)-\bar x-tw\big)\to z$ as $t\downarrow0$, i.e. $\xi(t)=\bar x+tw+\tfrac12t^2z+o(t^2)$, which is exactly the paper's construction and implies $\xi(t)\to\bar x$ and $\xi'_+(0)=w$.
-- source:
--   Mohammadi, Mordukhovich, Sarabi, Variational analysis of composite models with applications to continuous optimization, arXiv:1905.08837v2, p. 16, Proposition 4.3(ii); arc derivatives as defined on p. 8 after (2.17)

import Mathlib
import Definitions.Def_Subamenable_EpiDiff_Composite

open Filter Topology

namespace Subamenable.EpiDiff

theorem proposition_4_3_ii {n m : ℕ} (phi : E n → EReal) (theta : E m → EReal)
    (f : E n → E m) (xbar : E n)
    (h : IsFullySubamenableRep phi theta f xbar) (w z : E n)
    (hw : w ∈ tangentCone (f ⁻¹' dom theta) xbar)
    (hz : fderiv ℝ f xbar z + fderiv ℝ (fderiv ℝ f) xbar w w ∈
      secondTangentSet (dom theta) (f xbar) (fderiv ℝ f xbar w)) :
    z ∈ secondTangentSet (f ⁻¹' dom theta) xbar w ∧
      ∃ xi : ℝ → E n, (∀ᶠ t in 𝓝[>] (0 : ℝ), xi t ∈ f ⁻¹' dom theta) ∧
        Tendsto (fun t : ℝ => (2 / t ^ 2) • (xi t - xbar - t • w))
          (𝓝[>] (0 : ℝ)) (𝓝 z) := by sorry

end Subamenable.EpiDiff
