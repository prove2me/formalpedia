-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_lemma_4_16
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.lemma_4_16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:27:04.534532+00:00
-- url     : https://prove2.me/theorems/6879e46c-4e48-45a4-a4c7-387157c4e579
-- title:
--   Lemma 4.16
-- statement:
--   Let $s,\sigma>-1$ and $0<\gamma<1$. Principal-power composition $f_\gamma(z)=f(z^\gamma)$ defines continuous maps
--
--   $$\mathcal D_s\longrightarrow\mathcal D_\sigma^\infty\cap\mathcal H_{\pi/2}.$$
--
--   Both target norms have bounds by constants depending only on $s,\sigma,\gamma$ times $\|f\|_{\mathcal D_s}$. This makes the membership assertion and both continuity assertions precise.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 24, Lemma 4.16

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Lemma 4.16, arXiv:2202.03143v1, PDF page(s) 24. Source correction: Source correction resolved from the cited original: the survey p.24 prints an unbound H_psi in the final sentence. arXiv:2101.05083v2, Corollary 4.14, PDF p.38, explicitly gives the second norm bound into H_(pi/2). Changed the final codomain to pi/2, retaining the entire membership and continuity result. Original plan hard is superseded by this verified locator; independent moderation of the correction remains pending. -/
theorem lemma_4_16
(s sigma gamma : ℝ) (hs : -1 < s) (hsigma : -1 < sigma)
(hgamma : 0 < gamma) (hgamma1 : gamma < 1) :
    (∃ C : ℝ, 0 < C ∧ ∀ f, D s f → DBounded sigma (powerPull gamma f) ∧
      dBoundedSize sigma (powerPull gamma f) ≤ ENNReal.ofReal C * dSize s f) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f, D s f → HardySobolevClass (Real.pi / 2) (powerPull gamma f) ∧
      hSize (Real.pi / 2) (powerPull gamma f) ≤ ENNReal.ofReal C * dSize s f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
