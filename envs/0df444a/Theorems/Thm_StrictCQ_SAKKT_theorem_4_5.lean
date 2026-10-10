-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_theorem_4_5
-- name    : StrictCQ.SAKKT.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:55.689734+00:00
-- url     : https://prove2.me/theorems/17070617-0755-4bf9-bb1e-821511b74df7
-- title:
--   Theorem 4.5, p. 11 — SAKKT-regularity is the weakest strict constraint qualification associated with SAKKT
-- statement:
--   Consider problem (1.1) with continuously differentiable constraint functions $h_1,\dots,h_m$, $g_1,\dots,g_p$ on $\mathbb R^n$, and let $x^*$ be a feasible point. Then
--
--   $$x^*\ \text{is SAKKT-regular}\iff\Big(\text{for every } C^1 \text{ objective } f:\ \text{SAKKT holds at } x^* \text{ for } f\ \Longrightarrow\ \text{KKT holds at } x^* \text{ for } f\Big).$$
--
--   Here SAKKT-regularity (Definition 4.3) is the outer semicontinuity $\limsup_{x\to x^*}N_{\Omega(x,0)}(x)\subset N_{\Omega(x^*,0)}(x^*)$, where $\Omega(x,0)$ is the linearization of the equality constraints and of the inequality constraints that are active or violated at $x$; SAKKT asks for $x^k\to x^*$ and multipliers $\lambda^k$, $\mu^k\ge0$ with $\mu_j^k=0$ whenever $g_j(x^k)<0$ and with the KKT residual tending to zero.
--
--   The forward implication says that SAKKT-regularity is a strict constraint qualification for SAKKT; the backward implication says that every constraint property which makes SAKKT imply KKT for all objectives implies SAKKT-regularity. Together they make SAKKT-regularity the weakest such property.
--
--   **Formalization Note** "Smooth objective" is read as $\mathrm C^1$, which is all either direction uses. The objective is quantified inside the equivalence, for fixed constraints and a fixed feasible $x^*$. KKT is the multiplier form with sign and complementarity conditions.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 11, Theorem 4.5

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- Theorem 4.5: at a feasible `xs`, SAKKT-regularity holds iff, for every `C¹` objective `f`,
SAKKT at `xs` implies KKT at `xs`; i.e. SAKKT-regularity is the weakest strict constraint
qualification associated with SAKKT. -/
theorem theorem_4_5 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    C.SAKKTRegular xs ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 f → C.SAKKT f xs → C.IsKKT f xs := by sorry

end StrictCQ.SAKKT
