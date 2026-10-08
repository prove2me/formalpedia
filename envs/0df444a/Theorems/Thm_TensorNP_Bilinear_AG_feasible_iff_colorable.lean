-- Prove2me | Theorems.Thm_TensorNP_Bilinear_AG_feasible_iff_colorable
-- name    : TensorNP.Bilinear.AG_feasible_iff_colorable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:51.873366+00:00
-- url     : https://prove2.me/theorems/2e9f211e-c054-4287-ae95-455dc86c2296
-- title:
--   Proof of Theorem 3.7 — system (9) for $\mathcal A_G$ has a nonzero complex solution iff $G$ is 3-colorable
-- statement:
--   Let $G$ be a simple graph on $v \geq 1$ vertices and let $\mathcal A_G \in \mathbb Z^{l\times m\times n}$, $l = v(2v+5)$, $m = n = 2v+1$, be the tensor of the proof of Theorem 3.7 (minors, cube-root slices and edge slices). Then
--   $$
--   \exists\, \mathbf u \in \mathbb C^{l}\setminus\{0\},\ \mathbf v \in \mathbb C^{m}\setminus\{0\},\ \mathbf w \in \mathbb C^{n}\setminus\{0\} \text{ solving (9) for } \mathcal A_G \iff G \text{ is 3-colorable}.
--   $$
--
--   This is the correctness of the reduction of Theorem 3.7 over $\mathbb C$: the map $G \mapsto \mathcal A_G$ sends yes-instances of 3-colorability to yes-instances of tensor bilinear feasibility and no-instances to no-instances.
--
--   **Formalization Note** The hypothesis $v \geq 1$ is added. For $v = 0$ the tensor has $l = 0$ slices, so no nonzero $\mathbf u \in \mathbb C^0$ exists and (9) is infeasible, while the empty graph is 3-colorable; the paper's count $l = v(2v+5) > 4v+2$ also needs $v \geq 1$. The integer entries of $\mathcal A_G$ are read in $\mathbb C$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:17, proof of Theorem 3.7

import Mathlib
import Definitions.Def_TensorNP_Bilinear_Feasibility
import Definitions.Def_TensorNP_Bilinear_Construction

namespace TensorNP.Bilinear

/-- Proof of Theorem 3.7 (p. 0:17): for a graph `G` on `v ≥ 1` vertices, the system (9) for the
tensor `A_G` has a solution with `u, v, w` all nonzero complex vectors iff `G` is 3-colorable. -/
theorem AG_feasible_iff_colorable {v : ℕ} (G : SimpleGraph (Fin v)) (hv : 0 < v) :
    TBF (fun s p q => (AG G s p q : ℂ)) ↔ G.Colorable 3 := by sorry

end TensorNP.Bilinear
