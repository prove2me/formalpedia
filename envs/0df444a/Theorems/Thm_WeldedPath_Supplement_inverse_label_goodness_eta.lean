-- Prove2me | Theorems.Thm_WeldedPath_Supplement_inverse_label_goodness_eta
-- name    : WeldedPath.Supplement.inverse_label_goodness_eta
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:37.419704+00:00
-- url     : https://prove2.me/theorems/c5638c91-fee5-4123-a4bc-6efe9dbcd6b0
-- title:
--   Inverse-label goodness in both directions, with $\eta^{\mathrm{step}}$ leakage
-- statement:
--   Fix the explicit large choice $C_0=2^{40}$ in the size budget (49). There is an absolute constant $C>0$ such that, for even $n\ge16$, $l\in[2,n-4]$, every valid instance, and $t\le6q+6$ satisfying (49), both inverse-label directions have good-space leakage at most $C\eta_t^{\mathrm{step}}$:
--   $$
--   \|(1-\Pi_{t+1}^{\mathrm{good}})U\Pi_t^{\mathrm{good}}\|\le C\eta_t^{\mathrm{step}},
--   \qquad U\in\{(\mathrm{pC}^{\mathrm{inv}}_{\mathrm{lab}})^\dagger,\mathrm{pC}^{\mathrm{inv}}_{\mathrm{lab}}\}.
--   $$
--
--   Lemma 4.7 gives the sharper $O(\sqrt{t/M})$ inverse-label estimate; since $M=2^{2n}$ and $\epsilon_l=2^{-l}\le 2^{2n-4}$ under $l\le n-4$, this is also an $O(\eta_t^{\mathrm{step}})$ bound. The insertion and deletion analyses in its proof supply the two directions needed when telescoping the ordinary query.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 4.7 and its proof, pp.37–38; budget (49), p.26; $\eta^{\mathrm{step}}$ (61), p.32; application in Theorem 4.9, p.39.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

/-- The inverse-label compression factors preserve goodness, in both directions. -/
theorem WeldedPath.Supplement.inverse_label_goodness_eta :
    ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedPath.WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q + 6 →
      (2 : ℝ) ^ 40 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      (2 : ℝ) ^ 40 * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
        ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2 →
      (‖(1 - WeldedPath.Supplement.projGood l G (t + 1)).comp
          ((ContinuousLinearMap.adjoint (WeldedPath.Supplement.pCinvLab l G)).comp
            (WeldedPath.Supplement.projGood l G t))‖ ≤
        C * WeldedPath.Supplement.etaStep n l t) ∧
      (‖(1 - WeldedPath.Supplement.projGood l G (t + 1)).comp
          ((WeldedPath.Supplement.pCinvLab l G).comp
            (WeldedPath.Supplement.projGood l G t))‖ ≤
        C * WeldedPath.Supplement.etaStep n l t) := by sorry
