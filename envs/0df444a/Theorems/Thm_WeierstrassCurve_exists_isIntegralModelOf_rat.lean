-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isIntegralModelOf_rat
-- name    : WeierstrassCurve.exists_isIntegralModelOf_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/f195dcb2-0b26-515a-b3c1-99ea76bbd99b
-- title:
--   Every rational Weierstrass curve has an integral model
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{Q}$, i.e. a tuple of coefficients $a_1, a_2, a_3, a_4, a_6 \in \mathbb{Q}$. The assertion is that there exists a Weierstrass curve $W$ over $\mathbb{Z}$ such that `W.IsIntegralModelOf E` holds, which by definition means that there is an admissible change of variables $C$ over $\mathbb{Q}$ (an element of `VariableChange ℚ`, given by a unit $u$ of $\mathbb{Q}$ and three elements $r, s, t$) with $C \bullet E$ equal to the Weierstrass curve over $\mathbb{Q}$ obtained from $W$ by applying the ring homomorphism $\mathbb{Z} \to \mathbb{Q}$ to each coefficient. In other words, every Weierstrass curve over $\mathbb{Q}$ is $\mathbb{Q}$-isomorphic, via a change of variables over $\mathbb{Q}$, to the base change to $\mathbb{Q}$ of a Weierstrass curve with integral coefficients. No non-degeneracy hypothesis is imposed on $E$ (the discriminant may vanish), and no minimality of the resulting model is claimed.
--
--   This is the elementary existence of an integral Weierstrass model over $\mathbb{Z}$ for a curve given by a Weierstrass equation with rational coefficients; the minimal-model refinement, imposing non-vanishing discriminant and minimality of $|\Delta|$, is a separate statement. It is used in the construction of the rational torsion data underlying [`WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along`](thm.html#WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_along).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isIntegralModelOf_rat.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_isIntegralModelOf_rat (E : WeierstrassCurve ℚ) :
    ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E := by sorry
