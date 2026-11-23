-- Prove2me | Theorems.Thm_WeldedPath_Supplement_edge_goodness_eta
-- name    : WeldedPath.Supplement.edge_goodness_eta
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:07.156325+00:00
-- url     : https://prove2.me/theorems/1b0e723e-4f63-4d72-87d3-83fbc569790d
-- title:
--   Edge-compression goodness in both directions
-- statement:
--   Fix the explicit large choice $C_0=2^{40}$ in the size budget (49). There is an absolute constant $C>0$ such that, for even $n\ge16$, $l\in[2,n-4]$, every valid instance, and $t\le6q+6$ satisfying (49), controlled edge compression and its adjoint satisfy
--   $$
--   \|(1-\Pi_{t+1}^{\mathrm{good}})U\Pi_t^{\mathrm{good}}\|\le C\eta_t^{\mathrm{step}},
--   \qquad U\in\{\mathrm{pC}_{\mathrm{edge}}^\dagger,\mathrm{pC}_{\mathrm{edge}}\}.
--   $$
--
--   This is the two-direction form of Lemma 4.6 needed for the two occurrences of edge compression in the seven-factor formula (40). Its proof combines the insertion and deletion estimates (63)–(68).
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 4.6 and (62)–(68), pp.33–37; budget (49), p.26; application in Theorem 4.9, p.39.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

/-- The controlled edge compression preserves goodness with error of the order of the
step parameter, in both directions. -/
theorem WeldedPath.Supplement.edge_goodness_eta :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedPath.WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q + 6 →
      (2 : ℝ) ^ 40 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      (2 : ℝ) ^ 40 * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      (‖(1 - WeldedPath.Supplement.projGood l G (t + 1)).comp
          ((ContinuousLinearMap.adjoint (WeldedPath.Supplement.pCedge l G)).comp
            (WeldedPath.Supplement.projGood l G t))‖ ≤
        C * WeldedPath.Supplement.etaStep n l t) ∧
      (‖(1 - WeldedPath.Supplement.projGood l G (t + 1)).comp
          ((WeldedPath.Supplement.pCedge l G).comp
            (WeldedPath.Supplement.projGood l G t))‖ ≤
        C * WeldedPath.Supplement.etaStep n l t) := by sorry
