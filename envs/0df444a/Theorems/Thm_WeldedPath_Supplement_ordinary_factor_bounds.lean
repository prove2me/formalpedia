-- Prove2me | Theorems.Thm_WeldedPath_Supplement_ordinary_factor_bounds
-- name    : WeldedPath.Supplement.ordinary_factor_bounds
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:02.151639+00:00
-- url     : https://prove2.me/theorems/7928cca3-d3ed-46c0-b8a1-a3c3bcc8fc94
-- title:
--   Contraction bounds for the good projectors and ordinary query factors
-- statement:
--   For every welded-tree instance, every good-space projector $\Pi_t^{\mathrm{good}}$ and its complement $1-\Pi_t^{\mathrm{good}}$ has operator norm at most $1$. The inverse-label, edge, and forward-label compression operators, their Hilbert-space adjoints, and the XOR readout operator are also contractions.
--
--   These elementary bounds are the operator-norm input needed to telescope the seven factors of the ordinary compressed welded-tree query in the proof of Theorem 4.9.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Definition 3.4 and (30)–(40), pp.18–19; the good-space projector, p.27; telescoping in Theorem 4.9, p.39.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

/-- The good projectors and their complements are contractions, and every compression
factor of the ordinary compressed welded-tree oracle, including its adjoint, is a contraction. -/
theorem WeldedPath.Supplement.ordinary_factor_bounds (n l : ℕ) (G : WeldedInstance n) :
    (∀ t : ℕ, ‖WeldedPath.Supplement.projGood l G t‖ ≤ 1 ∧
      ‖1 - WeldedPath.Supplement.projGood l G t‖ ≤ 1) ∧
    (‖WeldedPath.Supplement.pCinvLab l G‖ ≤ 1 ∧
      ‖ContinuousLinearMap.adjoint (WeldedPath.Supplement.pCinvLab l G)‖ ≤ 1 ∧
      ‖WeldedPath.Supplement.pCedge l G‖ ≤ 1 ∧
      ‖ContinuousLinearMap.adjoint (WeldedPath.Supplement.pCedge l G)‖ ≤ 1 ∧
      ‖WeldedPath.Supplement.pCforLab l G‖ ≤ 1 ∧
      ‖ContinuousLinearMap.adjoint (WeldedPath.Supplement.pCforLab l G)‖ ≤ 1 ∧
      ‖WeldedPath.Supplement.xorP l G‖ ≤ 1) := by sorry
