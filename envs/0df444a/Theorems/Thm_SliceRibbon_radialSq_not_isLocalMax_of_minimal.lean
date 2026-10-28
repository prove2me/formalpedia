-- Prove2me | Theorems.Thm_SliceRibbon_radialSq_not_isLocalMax_of_minimal
-- name    : SliceRibbon.radialSq_not_isLocalMax_of_minimal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T11:55:33.760068+00:00
-- url     : https://prove2.me/theorems/479b5ed3-3533-4032-8c05-56900cf319f2
-- title:
--   On a minimal disc in $\mathbb R^4$ the radial function has no interior local maximum
-- statement:
--   Let $F:\mathbb R^2\to\mathbb R^4$ be $C^\infty$ with injective differential $dF_z$ at every point of the open unit disc $\{\|z\|<1\}$, and suppose $F$ is a minimal surface there (its mean curvature vector vanishes, in the sense of `IsMinimalOnDisk`). Then for every $z$ with $\|z\|<1$, the squared radial function $r_F(w)=\|F(w)\|^2$ does **not** have a local maximum at $z$:
--   $$\|z\|<1\ \Longrightarrow\ z \text{ is not a local maximum of } r_F.$$
--
--   This is the maximum-principle step in the minimal-surface approach to the slice–ribbon problem: on a minimal surface the Laplace–Beltrami operator of $\|x\|^2$ equals $4$, so the radial function is strictly subharmonic.
--
--   **Formalization Note** Local maximum is `IsLocalMax` for $r_F$ as a function on $\mathbb R^2$; no boundary behaviour or embeddedness is assumed.
-- source:
--   Open Problem Garden, 'Slice-ribbon problem' (posted by rybu, Nov 7 2009), http://www.openproblemgarden.org/op/slice_ribbon_problem; supporting lemma for [H] J. Hass, The geometry of the slice-ribbon problem, Math. Proc. Cambridge Philos. Soc. 94 (1983) 101-108 (maximum principle for the radial function on a minimal surface).

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric
open scoped ContDiff

namespace SliceRibbon

theorem radialSq_not_isLocalMax_of_minimal (F : R2 → R4) (hF : ContDiff ℝ ∞ F)
    (himm : ∀ z : R2, ‖z‖ < 1 → Function.Injective (fderiv ℝ F z))
    (hmin : IsMinimalOnDisk F) (z : R2) (hz : ‖z‖ < 1) :
    ¬ IsLocalMax (radialSq F) z := by sorry

end SliceRibbon
