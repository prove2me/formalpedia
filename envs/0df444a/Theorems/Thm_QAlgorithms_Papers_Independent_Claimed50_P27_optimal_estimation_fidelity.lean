-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_optimal_estimation_fidelity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.optimal_estimation_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:22:00.586076+00:00
-- url     : https://prove2.me/theorems/076e1f0c-e40b-4955-8f49-1489b1557617
-- title:
--   Optimal one-call estimate-and-reprepare cloning fidelity
-- statement:
--   Let $d\ge2$. In a one-call estimate-and-reprepare strategy, a fixed normalized bipartite probe is trained by applying the unknown unitary $U$ to one half. A physical POVM produces an estimated unitary $\widehat U$, and the output channel then applies $\widehat U\otimes\widehat U$ to the two external inputs. Optimize the normalized Haar-average global channel fidelity of Eq. (4) over these strategies. Every such strategy has fidelity at most the following value, and some strategy attains it:
--
--   $$F_{\mathrm{est}}=\begin{cases}5/16,&d=2,\\6/d^4,&d>2.\end{cases}$$
--
--   The measurement model allows discrete and continuous estimates through integrable positive operator densities relative to arbitrary finite reference measures. Probe and measurement are independent of the unknown gate. This evaluates the classical estimate-and-reprepare approach in the same two-copy channel figure of merit as the quantum cloner.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 4, Paragraph continuing from p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.3–4: the optimal estimate-and-reprepare cloning score, using the
estimation method attributed to [20]; the output channel applies the estimate twice. -/
theorem optimal_estimation_fidelity (d : ℕ) (hd : 2 ≤ d) :
    (∀ est : EstimateStrategy d,
      familyScore (estimateFamily est) ≤ estimationValue d) ∧
    ∃ est : EstimateStrategy d,
      familyScore (estimateFamily est) = estimationValue d := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
