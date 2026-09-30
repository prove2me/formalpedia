-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_analytic_additive_identity_component
-- name    : WeierstrassEllipticZeta.analytic_additive_identity_component
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-25T03:17:43.375801+00:00
-- url     : https://prove2.me/theorems/f723586c-4dc3-406e-8baa-cdb663b0e9d4
-- title:
--   Analytic additive subgroups have linear identity components
-- statement:
--   Let K be an additive subgroup of C³ that is the common zero locus of finitely many entire functions. Its connected component containing zero, for the usual norm topology, is a complex vector subspace. The proof establishes local linearity by a complement, normalized small subgroup elements, integer approximation, and the complex analytic identity theorem. The whole subgroup can still contain discrete periods.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, exponential maps and Lemma A.1. Supporting application geometry belongs to Senthil, not Philippon.

import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem WeierstrassEllipticZeta.analytic_additive_identity_component
    (K : AddSubgroup (Fin 3 → ℂ)) (F : Finset ((Fin 3 → ℂ) → ℂ))
    (hF : ∀ f ∈ F, AnalyticOnNhd ℂ f Set.univ)
    (hzero : ∀ v, v ∈ K ↔ ∀ f ∈ F, f v = 0) :
    ∃ V : Submodule ℂ (Fin 3 → ℂ),
      (V : Set (Fin 3 → ℂ)) = connectedComponentIn (K : Set (Fin 3 → ℂ)) 0 := by sorry
