-- Prove2me | Theorems.Thm_OrgDiversity_Optimal_netBen_eq_Kint
-- name    : OrgDiversity.Optimal.netBen_eq_Kint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:57.868258+00:00
-- url     : https://prove2.me/theorems/a93d4448-5685-4945-a3a1-563da3b0452b
-- title:
--   §3.3, p. 17 — K(b, d, σ) = ∫₀^{Pr[θ=d|σ]b} F, and K(x) = ∫₀ˣ F is increasing and strictly convex
-- statement:
--   Throughout, the standing assumptions of §2–§3.1 hold: $0<b_L<b_H$, $0<B_L<B_H$; the implementation cost $\tilde c$ has CDF $F$ with $F(0)=0$, $F$ strictly increasing and continuous on $[0,\infty)$, density $f=F'$ on $(0,\infty)$, and $F(b_H)\le 1$. Write $\Gamma=B_H/B_L$ and $\gamma=b_H/b_L$.
--
--   Let $\alpha\in(1/2,1]$. For every organization, project $d$ and signal $\sigma$, with $x=\Pr[\theta=d\mid\sigma]\,b$, IM's expected net benefit from implementing satisfies
--   $$K(b,d,\sigma)=p(b,d,\sigma)\,b-\int_0^{x}c\,f(c)\,dc=\int_0^{x}F(c)\,dc=K(x).$$
--   Moreover $K(x)=\int_0^xF(c)\,dc$ satisfies:
--   1. for every $x>0$, $K'(x)=F(x)>0$;
--   2. $K$ is strictly convex on $[0,\infty)$.
--
--   This is the paper's reduction of IM's payoffs to the single function $K$; the convexity of $K$ drives every comparison of information incentives in §3.3.
--
--   **Formalization Note** The page's "$\partial^2K(x)/\partial x^2>0$" is rendered as strict convexity of $K$ on $[0,\infty)$. Under the paper's assumptions $f$ may vanish at isolated points, so $f>0$ everywhere does not follow. Strict convexity is what the paper's later arguments use ("by the strict convexity of $K(\cdot)$", p. 18).
-- source:
--   Itoh & Morita, Information Acquisition, Decision Making, and Implementation in Organizations, SSRN 2751969 (version of August 5, 2019), p. 17, §3.3 (unnumbered display: K(b, d, ϕ), K(b, d, d), K(b, d, d′) and the properties of K)

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace OrgDiversity.Optimal

theorem netBen_eq_Kint (P : Params) (hP : P.Standing) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    (∀ (o : Org) (d : Proj) (σ : Sig), netBen P o α d σ = Kint P (post α d σ * imBen P o d)) ∧
    (∀ x : ℝ, 0 < x → HasDerivAt (Kint P) (P.F x) x ∧ 0 < P.F x) ∧
    StrictConvexOn ℝ (Set.Ici 0) (Kint P) := by sorry

end OrgDiversity.Optimal
