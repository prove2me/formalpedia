-- Prove2me | Theorems.Thm_SliceRibbon_isRibbon_iff_exists_ribbonSliceDisk
-- name    : SliceRibbon.isRibbon_iff_exists_ribbonSliceDisk
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T11:54:34.824142+00:00
-- url     : https://prove2.me/theorems/15914bbc-4730-4671-86bd-5545eaa31266
-- title:
--   Ribbon discs in $S^3$ versus ribbon slice discs in $B^4$
-- statement:
--   Write $S^3=\{x\in\mathbb R^4:\|x\|=1\}$, $B^4=\{x\in\mathbb R^4:\|x\|\le1\}$ and $D^2=\{z\in\mathbb R^2:\|z\|\le1\}$. A *knot* is the image $K=\gamma(\mathbb R)$ of a $C^\infty$, $1$-periodic map $\gamma:\mathbb R\to S^3$ that is injective on $[0,1)$ and has nowhere-vanishing velocity. Then $K$ bounds a ribbon disc in $S^3$ if and only if $K$ bounds a slice disc $F:D^2\to B^4$ on which the squared radial function $r_F(z)=\|F(z)\|^2$ is Morse in the open disc and has no local maxima there:
--   $$K\ \text{ribbon}\iff \exists\,F\ \text{slice disc for }K\ \text{with } r_F \text{ Morse on } \{\|z\|<1\}\text{ and without interior local maxima}.$$
--
--   This is the standard equivalence between Fox's $3$-dimensional definition of ribbon knots and the $4$-dimensional (Morse-theoretic) definition used in the study of the slice–ribbon problem; with it, the conjecture says that every slice disc can be replaced by one without interior maxima of the radial function.
--
--   **Formalization Note** `IsRibbon γ ↔ ∃ F, IsRibbonSliceDisk γ F`; Morse means that at each interior critical point the Hessian bilinear form of $r_F$ is non-degenerate.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; definition of ribbon knot linked from the problem statement (immersed-disc and radial-Morse characterisations); standard equivalence used e.g. in [H] J. Hass, The geometry of the slice-ribbon problem, Math. Proc. Cambridge Philos. Soc. 94 (1983) 101-108.

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric

namespace SliceRibbon

theorem isRibbon_iff_exists_ribbonSliceDisk (γ : ℝ → R4) (hγ : IsKnot γ) :
    IsRibbon γ ↔ ∃ F : R2 → R4, IsRibbonSliceDisk γ F := by sorry

end SliceRibbon
