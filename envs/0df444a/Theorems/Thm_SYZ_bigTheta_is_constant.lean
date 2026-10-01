-- Prove2me | Theorems.Thm_SYZ_bigTheta_is_constant
-- name    : SYZ.bigTheta_is_constant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T04:12:41.445493+00:00
-- url     : https://prove2.me/theorems/48a00b13-d744-4aea-ac79-eae59ce604c5
-- title:
--   SYZ Section 3: the natural $n$-form $\Theta$ on moduli space is closed
-- statement:
--   **Closedness of $\Theta$, Section 3 of Strominger–Yau–Zaslow.** On the moduli space of special Lagrangian deformations there is a natural $n$-form, defined on tangent vectors by
--   $$\Theta(\theta^{a_1},\dots,\theta^{a_n}) \;=\; \int_{L}\theta^{a_1}\wedge\cdots\wedge\theta^{a_n}.$$
--   In the coordinates of Section 3 — the harmonic gauge, in which the deformation forms change only by exact terms along the family — all of its derivatives vanish, so $\Theta$ is constant in the coordinates, and in particular closed:
--   $$\partial_c\,\Theta(\theta^{a_1},\dots,\theta^{a_n}) \;=\; 0 .$$
--
--   The paper uses this to extend $\Theta$ to a closed $n$-form $\Theta^{\mathcal M}$ on the full moduli space $\mathcal M$ in the complex coordinates $dz^a = dt^a + i\,ds^a$; when the brane is a torus, $b_1 = n$ and $\Theta^{\mathcal M}$ is a holomorphic $b_1$-form — the candidate Calabi–Yau form of the mirror.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, pp. 253-254, the natural n-form Theta on moduli space

import Definitions.Def_syz_flat_model

namespace SYZ

theorem bigTheta_is_constant {n m : ℕ} (S : SYZFamily n m)
    (a : Fin n → Fin m) (c : Fin m) (t : Dom m) :
    D (fun s => bigTheta S.F a s) c t = 0 := by sorry

end SYZ
