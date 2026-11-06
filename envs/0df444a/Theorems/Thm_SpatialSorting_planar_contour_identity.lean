-- Prove2me | Theorems.Thm_SpatialSorting_planar_contour_identity
-- name    : SpatialSorting.planar_contour_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:14.467373+00:00
-- url     : https://prove2.me/theorems/b3787d22-9940-483c-b96f-687193d60cb5
-- title:
--   Lemma 3.6 — planar restricted contour identity
-- statement:
--   Let $A$ be a cost matrix, $\beta\in\mathbb R$ and $\mathbf h\in\mathbb R^q$. For every finite region $V\subset\Lambda^\infty$, including regions with holes, and every colour $j$, the restricted fixed-collar partition function satisfies
--
--   $$Z^L_j(\beta,\mathbf h,V)=e^{h_j|V|}\sum_{\Gamma\in\mathcal P_j(V)}\prod_{\gamma\in\Gamma}w_j(\gamma),\tag{12}$$
--
--   where $\mathcal P_j(V)$ consists of the families of pairwise compatible type-$j$ contours admissible in $V$, and $w_j$ is the physical contour weight. Moreover, for the whole domain, $Z^L_0(D_L)$ is the physical variable-count partition function:
--
--   $$Z^L_0(\beta,\mathbf h,D_L)=\sum_{\sigma\in\Omega_{D_L}}W_{\mathbf h}(\sigma),\qquad W_{\mathbf h}(\sigma)=e^{-\beta H(\sigma)+\mathbf h\cdot\mathbf n_{D_L}(\sigma)},$$
--
--   since the two-layer collar of $D_L$ is exactly the wired boundary $B_L$, pinned to colour $0$.
--
--   The identity turns every restricted regional partition function into a polymer gas of contours, which is the input of the cluster expansion.
--
--   Differences from the source:
--   - encoding: 'Z^L_0(D_L) is the physical variable-count partition function' → Z^L_0(β, h, D_L) = Σ_{σ ∈ Ω_{D_L}} W_h(σ), over all colourings of I_L; reason: this is the paper's physical variable-count sum (p.19); the configurations of D_L with pinned collar B_L are the colourings of I_L
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.6, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Zres
import Definitions.Def_SpatialSorting_polymers
import Definitions.Def_SpatialSorting_w
import Definitions.Def_SpatialSorting_Wt
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 3.6 — planar restricted contour identity.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.6, p. 18 (PDF p. 19).

Formalization Notes:
- encoding: 'Z^L_0(D_L) is the physical variable-count partition function' → Z^L_0(β, h, D_L) = Σ_{σ ∈ Ω_{D_L}} W_h(σ), over all colourings of I_L. This is the paper's physical variable-count sum (p.19); the configurations of D_L with pinned collar B_L are the colourings of I_L. -/
theorem planar_contour_identity {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ)
    (hA : IsCostMatrix A) (β : ℝ) (h : Fin q → ℝ) :
    (∀ (j : Fin q) (V : Finset (ℤ × ℤ)),
      Zres A β h j V = Real.exp (h j * (V.card : ℝ)) *
        ∑ Γ ∈ polymers j V, ∏ γ ∈ Γ, w A β h j γ) ∧
    ∀ L : ℕ, Zres A β h 0 (D L) = ∑ σ : Coloring q L, Wt A β h σ := by sorry

end SpatialSorting
