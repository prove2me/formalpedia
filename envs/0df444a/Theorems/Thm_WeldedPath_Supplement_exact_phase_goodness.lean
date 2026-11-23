-- Prove2me | Theorems.Thm_WeldedPath_Supplement_exact_phase_goodness
-- name    : WeldedPath.Supplement.exact_phase_goodness
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:36.472708+00:00
-- url     : https://prove2.me/theorems/1c41ea6f-9112-4c62-af40-d2f1d8431e18
-- title:
--   Forward-label compression and XOR readout preserve goodness exactly
-- statement:
--   For even $n\ge16$, $l\in[2,n-4]$, and every valid welded-tree instance, forward-label insertion and deletion preserve goodness exactly:
--   $$
--   (1-\Pi_{t+1}^{\mathrm{good}})U\Pi_t^{\mathrm{good}}=0,
--   \qquad U\in\{(\mathrm{pC}^{\mathrm{for}}_{\mathrm{lab}})^\dagger,\mathrm{pC}^{\mathrm{for}}_{\mathrm{lab}}\}.
--   $$
--   The XOR readout $P$ does not change the record count and satisfies
--   $$
--   (1-\Pi_t^{\mathrm{good}})P\Pi_t^{\mathrm{good}}=0.
--   $$
--
--   These are the exact vanishing statements of Lemma 4.8, including the label-insertion and label-deletion cases used by the adjoint factor in (40).
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 4.8, p.38 (PDF p.37); factorization (40), p.19; application in Theorem 4.9, p.39.

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

/-- Forward-label compression and the XOR readout preserve the canonical good space exactly,
in both directions. -/
theorem WeldedPath.Supplement.exact_phase_goodness :
    ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
    ∀ G : WeldedPath.WeldedInstance n, G.IsValid → ∀ t : ℕ,
      ((1 - WeldedPath.Supplement.projGood l G (t + 1)).comp
          ((ContinuousLinearMap.adjoint (WeldedPath.Supplement.pCforLab l G)).comp
            (WeldedPath.Supplement.projGood l G t)) = 0 ∧
        (1 - WeldedPath.Supplement.projGood l G (t + 1)).comp
          ((WeldedPath.Supplement.pCforLab l G).comp
            (WeldedPath.Supplement.projGood l G t)) = 0) ∧
      (1 - WeldedPath.Supplement.projGood l G t).comp
        ((WeldedPath.Supplement.xorP l G).comp
          (WeldedPath.Supplement.projGood l G t)) = 0 := by sorry
