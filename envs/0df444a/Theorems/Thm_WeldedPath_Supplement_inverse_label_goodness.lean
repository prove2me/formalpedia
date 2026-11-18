-- Prove2me | Theorems.Thm_WeldedPath_Supplement_inverse_label_goodness
-- name    : WeldedPath.Supplement.inverse_label_goodness
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-18T00:57:43.222777+00:00
-- url     : https://prove2.me/theorems/66ded0f0-f76e-4e7f-9cc7-4a25a884cc30
-- title:
--   Inverse-label compression preserves goodness with explicit leakage bound
-- statement:
--   Let M=2^(2n), N=2^n, and let G be a valid welded-tree instance with n≥16 and 2≤l≤n−4. Let B contain the canonical boundary and avoid the weld vertices. Suppose t≤M and
--
--   \[(2t)|B|\frac4N\le\frac12,\qquad 2(2t)^3\frac{96(n+1)}N\le\frac12.\]
--
--   For the literal canonical inverse-label compression operator and canonical database good-space projectors,
--
--   \[\|(1-\Pi^{good}_{t+1}(B))\,pC^{inv}_{lab}\,\Pi^{good}_{t}(B)\|
--   \le\sqrt{\frac{16t}{M-t+1}}.\]
--
--   The query register is coherent and unrestricted. The conclusion is an operator-norm estimate on the entire good subspace, including superpositions across different forest descriptions.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1, Lemma4.7; explicit constants and coefficient-stability hypotheses.

import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

namespace WeldedPath.Supplement

theorem inverse_label_goodness {n l : ℕ} (G : WeldedInstance n)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (hBw : Disjoint B (Vweld n))
    (t : ℕ) (htM : t ≤ labelBound n)
    (hsurvive : (2 * (t : ℝ)) * (B.card : ℝ) * (4 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (hcollision : 2 * (2 * (t : ℝ)) ^ 3 * (96 * ((n : ℝ) + 1) / (2 : ℝ) ^ n) ≤ 1 / 2) :
    ‖((1 : Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G)) -
        projGoodB l G B (t+1)).comp ((pCinvLab l G).comp (projGoodB l G B t))‖ ≤
      Real.sqrt (16 * (t : ℝ) / ((labelBound n - t + 1 : ℕ) : ℝ)) := by
  sorry

end WeldedPath.Supplement
