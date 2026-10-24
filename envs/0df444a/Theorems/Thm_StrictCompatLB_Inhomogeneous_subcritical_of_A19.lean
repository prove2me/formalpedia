-- Prove2me | Theorems.Thm_StrictCompatLB_Inhomogeneous_subcritical_of_A19
-- name    : StrictCompatLB.Inhomogeneous.subcritical_of_A19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:31.109488+00:00
-- url     : https://prove2.me/theorems/d3df0115-fc32-4e03-b3ea-c8942c4891be
-- title:
--   (A.19) implies the subcriticality condition (3.2)
-- statement:
--   Let $\{G_N\}_{N \ge 1}$ be any sequence of bipartite compatibility graphs, $G_N = (V_N, W_N, E_N)$ with $|V_N| = N$ and $|W_N| = M(N)$, and let $d \ge 1$. If
--   $$\limsup_{N \to \infty} \max_{v \in V_N} \frac{N}{M(N)} \sum_{w \in W_N} \frac{\mathbb 1\{(v, w) \in E_N\}}{|N_w|} \le 1, \qquad\text{(A.19)}$$
--   then the sequence satisfies the subcriticality condition (3.2) of Definition 3.3 for the sampling size $d$.
--
--   The paper observes this reduction when $\gamma^U_w$ is the uniform distribution on $U$: with that choice the inner normalised sum in (3.2) equals $\mathbb 1\{(v, w) \in E_N\}/|N_w|$. It is the deterministic step that turns the almost-sure verification of (A.19) into subcriticality.
--
--   **Formalization Note** Subcriticality is the repaired form of Definition 3.3 (distributions only on nonempty $U$; normalisation $\binom{|N_w|}{\min(d, |N_w|)}$), under which the identity above holds exactly; see the definition item. The same reduction is posed in the sibling mission on Theorem 3.5.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 34, Appendix A, display (A.19)

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions

namespace StrictCompatLB.Inhomogeneous

/-- (A.19) reduction (Appendix A, p. 34): for any sequence of bipartite compatibility graphs and
any sampling size `d ≥ 1`, condition (A.19) implies the subcriticality condition (3.2) (the
uniform weights `γ^U_w(v) = 1 / |U|` witness it). -/
theorem subcritical_of_A19 (d : ℕ) (hd : 1 ≤ d) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (h : StrictCompatLB.RegularDegree.SatisfiesA19 M G) :
    StrictCompatLB.MeanField.IsSubcritical d M G := by sorry

end StrictCompatLB.Inhomogeneous
