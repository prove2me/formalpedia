-- Prove2me | Theorems.Thm_ReluMIP_Facet_proposition_2
-- name    : ReluMIP.Facet.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:10.753135+00:00
-- url     : https://prove2.me/theorems/bdbd2897-7378-4fc7-88f5-25cf79ab57b8
-- title:
--   Proposition 2, p. 6 — under strict activity each inequality in (6b) is facet-defining
-- statement:
--   Let $f(x)=w\cdot x+b$ with $w\in\mathbb R^\eta$, $b\in\mathbb R$, over the input box $[L,U]$ with $L_i<U_i$ for every $i$, and assume strict activity, $M^-(f)<0<M^+(f)$. Let $P$ be the convex hull of the points $(x,y,z)$ feasible with respect to formulation (6):
--   $$
--   y\ge w\cdot x+b,\qquad y\le\sum_{i\in I'}w_i\bigl(x_i-\breve L_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I'}w_i\breve U_i\Bigr)z\ \ \forall I'\subseteq\operatorname{supp}(w),\qquad (x,y,z)\in[L,U]\times\mathbb R_{\ge0}\times\{0,1\}.
--   $$
--   Then for every $I\subseteq\operatorname{supp}(w)$ the inequality (6b) for $I$,
--   $$
--   y\le\sum_{i\in I}w_i\bigl(x_i-\breve L_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve U_i\Bigr)z ,
--   $$
--   is facet-defining for $P$: it is valid on $P$, the face $F$ of $P$ on which it holds with equality is nonempty, and $\dim F=\dim P-1$.
--
--   Together with Proposition 1 (formulation (6) is ideal), this says that none of the exponentially many inequalities (6b) can be dropped: formulation (6) is minimal modulo variable bounds. The paper notes that strict activity is required for this result.
--
--   **Formalization Note** "Facet-defining" is not defined in the paper; the standard notion is used, with dimensions as `finrank` of the `vectorSpan` and $\dim F=\dim P-1$ written $\dim F+1=\dim P$. The polyhedron is the convex hull of the points of (6) (with $z\in\{0,1\}$), which by Proposition 1 equals the LP relaxation of (6); the hull is used so that the statement does not depend on Proposition 1. The bounds $L<U$ and strict activity are the paper's standing assumptions of §1.3. Indices are 0-based (`Fin η`).
-- source:
--   arXiv:1811.08359v2, Proposition 2, p. 6 (proof App. A.2, p. 15)

import Mathlib
import Definitions.Def_ReluMIP_Facet_Setting

namespace ReluMIP.Facet

/-- Proposition 2, p. 6 (arXiv:1811.08359v2): under the standing assumptions of §1.3
(`L < U` componentwise and strict activity `M⁻(f) < 0 < M⁺(f)`), each inequality (6b),
`y ≤ ∑_{i∈I} wᵢ(xᵢ − L̆ᵢ(1 − z)) + (b + ∑_{i∉I} wᵢŬᵢ) z` for `I ⊆ ReluMIP.Ideal.supp(w)`, is facet-defining for
the convex hull of the points feasible with respect to formulation (6). -/
theorem proposition_2 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) (hSA : ReluMIP.Ideal.StrictActivity w b L U) :
    ∀ I : Finset (Fin η), I ⊆ ReluMIP.Ideal.supp w →
      IsFacetDefining (convexHull ℝ (form6 w b L U))
        (fun p => p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2) := by sorry

end ReluMIP.Facet
