-- Prove2me | Theorems.Thm_RSF_twist_computation
-- name    : RSF.twist_computation
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-23T03:17:05.248031+00:00
-- url     : https://prove2.me/theorems/39b0503a-8f8b-42aa-9cba-af99fabd4ca4
-- title:
--   The upper shriek of the structure sheaf along a smooth map (Theorem 1.2.8)
-- statement:
--   Theorem 1.2.8 of the thesis: for a smooth map f of analytic adic spaces over Q_p of pure dimension d, the upper shriek of the structure sheaf is the structure sheaf of the source, Tate twisted by d and shifted by 2d: f^!(O_X^+a/p) = O_Y^+a/p(d)[2d]. The proof passes through the p-cohomological smoothness of the diamondified map, purity, and the Riemann-Hilbert correspondence, and identifies the relative dualizing sheaf up to which Poincare duality is stated.
--
--   **Formalization Note** The shift and the Tate twist are bundled operations of the abstract world; the isomorphism is encoded as an equality of objects.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), Theorem 1.2.8 (proved as Theorem 3.10.20).

import Mathlib
import Definitions.Def_RSF_cat
import Definitions.Def_RSF_geo

namespace RSF

/-!  Theorem 1.2.8 of the thesis: the computation of the upper shriek of the
structure sheaf along a smooth map of pure dimension d: it is the structure
sheaf of the source, Tate twisted by d and shifted by 2d. Together with
purity this identifies the relative dualizing sheaf, and with the proper
special case of Theorem 1.2.4 it produces the trace map whose perfectness
is Poincare duality.  -/

theorem twist_computation :
    ∀ (w : SixFunctorWorld) (X Y : w.Space) (f : w.Map Y X) (d : ℕ),
    w.IsAdicSmooth Y X f → w.IsPureDim Y X f d →
    w.ushriek Y X f (w.unit X) = w.shift Y (2 * d) (w.tateTwist Y d (w.unit Y)) := by
  sorry

end RSF
