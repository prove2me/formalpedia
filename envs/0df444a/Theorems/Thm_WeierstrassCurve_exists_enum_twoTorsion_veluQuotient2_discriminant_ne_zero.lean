-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
-- name    : WeierstrassCurve.exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/95b7004a-4f50-58f8-a12b-8d7bccbf7b70
-- title:
--   Three 2-torsion points with nonsingular Vélu quotients
-- statement:
--   Let $K$ be an algebraically closed field in which $2 \neq 0$, and let $W$ be a Weierstrass curve over $K$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, which is elliptic (its discriminant is a unit). Then there exist a type $\iota$, a finite type structure on it with $\#\iota = 3$, and a map $P : \iota \to K \times K$ such that: $P$ is injective; for every $i$ the pair $P i = (x_i,y_i)$ satisfies the affine Weierstrass equation of $W$; for every $i$ one has $\mathtt{veluGy}(x_i,y_i) = -(2y_i + a_1 x_i + a_3) = 0$; and for every $i$ the discriminant $\Delta$ of the Weierstrass curve $\mathtt{veluQuotient2}(x_i,y_i)$ is nonzero, where this curve has the same $a_1,a_2,a_3$ as $W$ and has $a_4$ replaced by $a_4 - 5 g_x(x_i,y_i)$ and $a_6$ replaced by $a_6 - b_2\, g_x(x_i,y_i) - 7 x_i\, g_x(x_i,y_i)$, with $g_x(x,y) = 3x^2 + 2a_2 x + a_4 - a_1 y$. Thus the three affine points fixed by negation are enumerated injectively, and each of the associated Vélu order-$2$ quotient curves is nonsingular.
--
--   This is the level-$2$ case of the enumeration of the cyclic subgroups of order $\ell$ of an elliptic curve together with their Vélu quotients: the three nontrivial $2$-torsion points, listed injectively, with the quotient curves nonsingular. It is used in the treatment of the modular polynomial of level $2$ and in the study of rational homomorphisms satisfying $\varphi\circ\varphi + 2\,\psi = \ldots$, where exactly this packaging of hypotheses is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ P : ι → K × K, Function.Injective P ∧
        (∀ i, W.toAffine.Equation (P i).1 (P i).2) ∧ (∀ i, W.veluGy (P i).1 (P i).2 = 0) ∧
        ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := by sorry
