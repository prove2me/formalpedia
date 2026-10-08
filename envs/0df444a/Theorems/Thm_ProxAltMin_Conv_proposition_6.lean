-- Prove2me | Theorems.Thm_ProxAltMin_Conv_proposition_6
-- name    : ProxAltMin.Conv.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:58.959379+00:00
-- url     : https://prove2.me/theorems/2edf4e7a-792e-42ed-b2ea-e44cbca5569d
-- title:
--   Proposition 6 — limit points of the proximal alternating sequence are critical, and L is finite and constant on them
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1), let $(x_k,y_k)$ comply with (5)–(6), and let $\omega(x_0,y_0)$ be the set (possibly empty) of its limit points. Then:
--   1. if $(x_k,y_k)$ is bounded, $\omega(x_0,y_0)$ is a nonempty compact connected set and
--   $$d\big((x_k,y_k),\omega(x_0,y_0)\big)\to0\quad(k\to+\infty);$$
--   2. $\omega(x_0,y_0)\subset\operatorname{crit}L$, i.e. $0\in\partial L(\bar z)$ for every $\bar z\in\omega(x_0,y_0)$;
--   3. $L$ is finite and constant on $\omega(x_0,y_0)$, equal to $\inf_{k\in\mathbb N}L(x_k,y_k)=\lim_{k\to+\infty}L(x_k,y_k)$.
--
--   This is the first convergence result for the scheme: subsequential convergence to critical points, with a common critical value.
--
--   **Formalization Note** A limit point is a cluster point of the sequence (`MapClusterPt`). In 3, the convergence $L(x_k,y_k)\to\inf_kL(x_k,y_k)$ in $\mathbb R\cup\{\pm\infty\}$ is stated unconditionally; finiteness and the value of $L$ on $\omega$ are stated for each limit point.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 7, Proposition 6

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Proposition 6 (p. 7): let `(xₖ, yₖ)` comply with (5)–(6) under (H), (H1), and let `ω(x₀, y₀)` be
the set (possibly empty) of its limit points (cluster points of the sequence). Then
(i) if the sequence is bounded, `ω(x₀, y₀)` is nonempty, compact and connected, and
`d((xₖ, yₖ), ω(x₀, y₀)) → 0`;
(ii) `ω(x₀, y₀) ⊂ crit L`;
(iii) `L` is finite and constant on `ω(x₀, y₀)`, equal to `inf_k L(xₖ, yₖ) = lim_k L(xₖ, yₖ)`. -/
theorem proposition_6 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y) :
    (Bornology.IsBounded (Set.range (fun k => pt (x k) (y k))) →
      {w : Z n m | MapClusterPt w atTop (fun k => pt (x k) (y k))}.Nonempty ∧
      IsCompact {w : Z n m | MapClusterPt w atTop (fun k => pt (x k) (y k))} ∧
      IsConnected {w : Z n m | MapClusterPt w atTop (fun k => pt (x k) (y k))} ∧
      Tendsto (fun k => Metric.infDist (pt (x k) (y k))
        {w : Z n m | MapClusterPt w atTop (fun k => pt (x k) (y k))}) atTop (𝓝 0)) ∧
    (∀ w : Z n m, MapClusterPt w atTop (fun k => pt (x k) (y k)) →
      (0 : Z n m) ∈ LimitingSubdiff (L f Q g) w) ∧
    (∀ w : Z n m, MapClusterPt w atTop (fun k => pt (x k) (y k)) →
      L f Q g w ≠ ⊤ ∧ L f Q g w ≠ ⊥ ∧ L f Q g w = ⨅ k, L f Q g (pt (x k) (y k))) ∧
    Tendsto (fun k => L f Q g (pt (x k) (y k))) atTop (𝓝 (⨅ k, L f Q g (pt (x k) (y k)))) := by sorry

end ProxAltMin.Conv
