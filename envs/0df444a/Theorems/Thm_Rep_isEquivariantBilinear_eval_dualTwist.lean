-- Prove2me | Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
-- name    : Rep.isEquivariantBilinear_eval_dualTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/7772730b-702d-58f8-9cb8-79d77442a058
-- title:
--   Equivariance of the evaluation pairing M × M^∨(χ) → k(χ)
-- statement:
--   Let $k$ be a field, $G$ a group, $M$ a $k$-linear representation of $G$ (an object of `Rep k G`), and $\chi \colon G \to k^\times$ a group homomorphism. Two further representations are formed from these data: `M.dualTwist χ`, whose underlying space is the $k$-linear dual of $M$ and whose action of $g$ is $\chi(g)$ times the contragredient action, i.e. $f \mapsto \chi(g)\,(f \circ \rho_M(g^{-1}))$; and [`groupCohomology.ofChar χ`](def/DualSelmer_ExtConditions.html#L13), whose underlying space is $k$ itself with $g$ acting as multiplication by $\chi(g)$, that is, the trivial representation twisted by $\chi$. The assertion is that the evaluation map `Module.Dual.eval k M`, namely $m \mapsto (f \mapsto f(m))$, regarded as a $k$-bilinear map $M \to (M^\vee(\chi)) \to k(\chi)$, satisfies [`Rep.IsEquivariantBilinear`](def/GroupCohomology_CupProduct.html#L13): for every $g \in G$, every $m \in M$ and every $f$ in the dual, $$\langle \rho_M(g)\,m,\ \rho_{M^\vee(\chi)}(g)\,f\rangle = \rho_{k(\chi)}(g)\,\langle m, f\rangle,$$ equivalently $(g\cdot f)(g\cdot m) = \chi(g)\,f(m)$.
--
--   This records that the Cartier–Tate duality pairing between a representation and its $\chi$-twisted dual takes values equivariantly in the character module $k(\chi)$, so that it may be fed into the cup-product and Selmer-duality machinery as an equivariant bilinear pairing. It is used in the local-duality and dual-Selmer arguments, for instance in the local bridge statements comparing units and local characters and in the bijectivity criteria for the relevant comparison maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isEquivariantBilinear_eval_dualTwist.lean

import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_CupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.isEquivariantBilinear_eval_dualTwist {k G : Type u} [Field k] [Group G]
    (M : Rep.{u} k G) (χ : G →* kˣ) :
    Rep.IsEquivariantBilinear M (M.dualTwist χ) (groupCohomology.ofChar χ)
      (Module.Dual.eval k M : M →ₗ[k] M.dualTwist χ →ₗ[k] groupCohomology.ofChar χ) := by sorry
