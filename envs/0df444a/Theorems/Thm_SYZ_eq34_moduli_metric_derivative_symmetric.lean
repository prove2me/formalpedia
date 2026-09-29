-- Prove2me | Theorems.Thm_SYZ_eq34_moduli_metric_derivative_symmetric
-- name    : SYZ.eq34_moduli_metric_derivative_symmetric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T04:07:49.770184+00:00
-- url     : https://prove2.me/theorems/268deaf8-a65e-4519-9520-0280d9c26856
-- title:
--   SYZ Eq. (3.4): $\partial_a g_{bc} = \partial_b g_{ac}$
-- statement:
--   **Equation (3.4) of Strominger–Yau–Zaslow.** Let $F$ be a smooth $m$-parameter family of special Lagrangian tori in a flat Calabi–Yau, normalized as in Section 3 so that each deformation $1$-form $\theta^a$ is harmonic for the induced metric and has constant periods. Let
--   $$g_{ab}(t) \;=\; \int_{L} g^{ij}\,\theta^a_i\,\theta^b_j\,\sqrt{\det g}\;d^n x$$
--   be the $L^2$ (McLean) metric on the moduli parameters. Then its first derivatives are totally symmetric:
--   $$\partial_a\, g_{bc} \;=\; \partial_b\, g_{ac}.$$
--
--   This is the technical heart of Section 3. Differentiating $g_{bc}$ produces four contributions — from $\theta^b$, from $\theta^c$, from the inverse metric and from the volume density. The first two are exact forms paired against co-closed forms, so they integrate to zero over the compact brane; the volume-density term is proportional to the mean curvature, which vanishes because a special Lagrangian submanifold is minimal; what remains is $-2\int_L h_{ijk}\,w_a^i w_b^j w_c^k$, totally symmetric because $h$ is a symmetric $3$-tensor.
--
--   Equivalently, the McLean metric is locally the Hessian of a potential, so the moduli space carries an affine-Kähler (Hessian) structure. This is the statement from which the Kähler property of the D-brane moduli space follows.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, p. 253, Eq. (3.4)

import Definitions.Def_syz_flat_model

namespace SYZ

theorem eq34_moduli_metric_derivative_symmetric {n m : ℕ}
    (S : SYZFamily n m) (a b c : Fin m) (t : Dom m) :
    D (fun s => gMod S.F b c s) a t = D (fun s => gMod S.F a c s) b t := by sorry

end SYZ
