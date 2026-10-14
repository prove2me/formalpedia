-- Prove2me | Theorems.Thm_SliceRibbon_isRibbon_of_minimal_sliceDisk
-- name    : SliceRibbon.isRibbon_of_minimal_sliceDisk
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T11:56:11.920981+00:00
-- url     : https://prove2.me/theorems/3f18ece0-24cd-4e4d-a924-1684b81d0b50
-- title:
--   Knots bounding minimal discs in $B^4$ are ribbon (Hass)
-- statement:
--   Write $S^3=\{x\in\mathbb R^4:\|x\|=1\}$, $B^4=\{x\in\mathbb R^4:\|x\|\le1\}$ and $D^2=\{z\in\mathbb R^2:\|z\|\le1\}$. A *knot* is the image $K=\gamma(\mathbb R)$ of a $C^\infty$, $1$-periodic map $\gamma:\mathbb R\to S^3$ that is injective on $[0,1)$ and has nowhere-vanishing velocity. Suppose $K$ bounds a slice disc $F:D^2\to B^4$ (smoothly embedded, transverse to $S^3$ along its boundary $K$) which is a minimal surface for the Euclidean metric of $\mathbb R^4$, i.e. its mean curvature vector vanishes at every interior point. Then
--   $$K\ \text{is ribbon}.$$
--
--   Thus a potential counterexample to the slice–ribbon conjecture cannot bound a minimal slice disc.
--
--   **Formalization Note** Minimality is `IsMinimalOnDisk F`: with first fundamental form $E,G',G$, the vector $G\,\partial_0\partial_0F-2G'\,\partial_0\partial_1F+E\,\partial_1\partial_1F$ lies in the image of $dF_z$ for all $\|z\|<1$.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; Bibliography [H] J. Hass, The geometry of the slice-ribbon problem, Math. Proc. Cambridge Philos. Soc. 94 (1983), no. 1, 101-108.

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric

namespace SliceRibbon

theorem isRibbon_of_minimal_sliceDisk (γ : ℝ → R4) (hγ : IsKnot γ) (F : R2 → R4)
    (hF : IsSliceDisk γ F) (hmin : IsMinimalOnDisk F) :
    IsRibbon γ := by sorry

end SliceRibbon
