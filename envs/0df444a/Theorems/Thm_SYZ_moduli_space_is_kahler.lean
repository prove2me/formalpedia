-- Prove2me | Theorems.Thm_SYZ_moduli_space_is_kahler
-- name    : SYZ.moduli_space_is_kahler
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T04:16:24.491927+00:00
-- url     : https://prove2.me/theorems/99d502a6-8f92-4cb2-ae58-31829f0bcc64
-- title:
--   SYZ Section 3: the D-brane moduli space is Kähler
-- statement:
--   **The conclusion of Section 3 of Strominger–Yau–Zaslow: the D-brane moduli space is Kähler.**
--
--   Let $F$ be a smooth $m$-parameter family of special Lagrangian $n$-tori in a flat Calabi–Yau, all with the same periods, normalized as in Section 3: each deformation $1$-form
--   $$\theta^a_i \;=\; \omega\!\left(\partial_{t^a} f,\ \partial_i f\right)$$
--   is harmonic for the induced metric of its member, and the cohomology class of each $\theta^a$ is constant along the family. Let
--   $$g_{ab}(t) \;=\; \int_{L} g^{ij}\,\theta^a_i\,\theta^b_j\,\sqrt{\det g}\;d^n x$$
--   be the $L^2$ (McLean) metric on the moduli parameters.
--
--   The full moduli space $\mathcal M$ of the paper records both the brane and its flat $U(1)$ connection; the connections at a fixed brane form a torus of the same dimension, with coordinates $s^a$. Model $\mathcal M$ by $\mathbb R^m \times \mathbb R^m$ with coordinates $(t^a, s^a)$, carrying the block-diagonal metric
--   $$G \;=\; g_{ab}\,(dt^a dt^b + ds^a ds^b)$$
--   and the constant almost complex structure $\mathcal J(\partial_{t^a}) = \partial_{s^a}$, $\mathcal J(\partial_{s^a}) = -\partial_{t^a}$, with fundamental $2$-form $\omega_{\mathcal M}(X,Y) = G(\mathcal J X, Y)$. Then
--   $$d\,\omega_{\mathcal M} \;=\; 0 ,$$
--   and since $\mathcal J$ is constant in these coordinates it is integrable, so $(\mathcal M, G, \mathcal J)$ is a Kähler manifold.
--
--   This is the assertion of the paper that "with a certain natural metric, the D-brane moduli space has a Kähler structure". The route through the milestones is: Propositions 1 and 2 identify the deformations preserving the special Lagrangian condition with the harmonic $1$-forms; Proposition 4 and Eq. (A.2) compute how the induced metric and the harmonic representatives move; Eq. (3.4) assembles these into the total symmetry $\partial_a g_{bc} = \partial_b g_{ac}$; and the Hessian-implies-Kähler milestone converts that symmetry into closedness of $\omega_{\mathcal M}$.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, pp. 248-254, Section 3 (D-brane moduli space); conclusion stated on p. 248 and derived from Eq. (3.4) on p. 253

import Definitions.Def_syz_flat_model

namespace SYZ

theorem moduli_space_is_kahler {n m : ℕ} (S : SYZFamily n m) :
    IsClosed2Form (moduliKahler (fun t => Matrix.of fun a b => gMod S.F a b t)) := by sorry

end SYZ
