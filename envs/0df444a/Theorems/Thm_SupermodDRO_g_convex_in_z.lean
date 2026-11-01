-- Prove2me | Theorems.Thm_SupermodDRO_g_convex_in_z
-- name    : SupermodDRO.g_convex_in_z
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:45.577391+00:00
-- url     : https://prove2.me/theorems/e8bb2eec-5ee8-4303-9fac-ebd597c63988
-- title:
--   Proof of Proposition 1, p.41 — $g(x,z)$ is convex in $z$
-- statement:
--   Let $g(x,z)=\min\{b^\top y : Wx+Uy\ge Vz+v^0\}\in[-\infty,+\infty]$ be the second-stage cost (1). For every first-stage decision $x$, the function $z\mapsto g(x,z)$ is convex: its epigraph
--   $$
--   \{(z,t)\in\mathbb R^n\times\mathbb R \;:\; g(x,z)\le t\}
--   $$
--   is a convex set.
--
--   The paper invokes this fact (citing Birge and Louveaux, Theorem 2, §3.1) in the proof of Proposition 1, to conclude that a worst-case distribution with three-point marginals sees every infeasible realization.
--
--   **Formalization Note** Convexity of an extended-valued function is convexity of its epigraph; no finiteness is assumed. The textbook theorem itself is a separate platform item for the standard-form recourse program; this item is the instance in which $z$ enters the right-hand side through $Vz$.
--
--   Differences from the source:
--   - encoding: g(x, z) is convex in z → the epigraph {(z, t) | g(x, z) ≤ t} is convex; reason: the standard definition of convexity for a [−∞, ∞]-valued function; same instances
--   - encoding: g(x, z) = min b⊤y, with g(x, z) = ∞ if (1) is infeasible → the infimum in EReal: ⊤ on an empty feasible set, ⊥ on an unbounded program; reason: same value whenever (1) is infeasible or has an optimal value; the paper never writes the unbounded case
--   - encoding: [n] indexed from 1 → Fin n indexed from 0; reason: Lean convention; same instances
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proof of Proposition 1 (App. C.1), p.41

import Mathlib
import Definitions.Def_SupermodDRO_secondStageCost

namespace SupermodDRO

/-- **`g(x, z)` is convex in `z`.** Long, Qi & Zhang, *Supermodularity in Two-Stage Distributionally
Robust Optimization*, author manuscript (June 2022), Proof of Proposition 1 (App. C.1), p.41: "Since
function g(x, z) is convex in z (see Theorem 2, Section 3.1 in Birge and Louveaux (2011)), there must
exist z″ ∈ supp(ℙ″) such that g(x′, z″) = ∞."

For every first-stage decision `x`, the extended-real function `z ↦ g(x, z)` of (1) is convex: its
epigraph `{(z, t) ∈ ℝⁿ × ℝ | g(x, z) ≤ t}` is a convex set.

**Formalization Note** Convexity of a function with values in `[−∞, ∞]` is convexity of its
epigraph; this needs no finiteness assumption. The cited textbook result (Birge & Louveaux,
Ch. 3, Theorem 2) is a separate platform item (`StochasticProg.RecourseKKT.theorem_2`, for the
standard-form recourse program); this item is the paper's own instance, where `z` enters the
right-hand side of (1) through `Vz`. A related proved result is
`Wets1974.Stability.LPValue_polyhedral_or_bot`. -/
theorem g_convex_in_z {l m r n : ℕ} (W : Matrix (Fin r) (Fin l) ℝ) (U : Matrix (Fin r) (Fin m) ℝ)
    (V : Matrix (Fin r) (Fin n) ℝ) (v0 : Fin r → ℝ) (b : Fin m → ℝ) (x : Fin l → ℝ) :
    Convex ℝ {p : (Fin n → ℝ) × ℝ | secondStageCost W U V v0 b x p.1 ≤ (p.2 : EReal)} := by sorry

end SupermodDRO
