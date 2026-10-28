-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_nearPureNormEntropyAsymptotics
-- name    : QAlgorithms.Papers.Independent.Support50.P31.nearPureNormEntropyAsymptotics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:29:53.097089+00:00
-- url     : https://prove2.me/theorems/3ba02a2a-065c-45b0-95de-773303836b6f
-- title:
--   Norm and entropy asymptotics near a pure state
-- statement:
--   Fix a nonzero finite-dimensional complex Hilbert space and a family of density matrices $\rho_\epsilon$, defined for all sufficiently small $\epsilon>0$. Suppose
--   $$
--   \|\rho_\epsilon\|_{\mathrm{op}}=1-\epsilon+o(\epsilon)
--   \quad(\epsilon\downarrow0).
--   $$
--   Then, for every fixed $1<p\le\infty$,
--   $$
--   \|\rho_\epsilon\|_p=1-\epsilon+o(\epsilon),\qquad
--   H(\rho_\epsilon)=-\epsilon\log\epsilon+o(\epsilon\log\epsilon).
--   $$
--   Here $p=\infty$ denotes the assumed operator-norm case, $H$ uses natural logarithms with $0\log0=0$, and little-o is along positive parameters. These qualitative expansions describe a nearly pure spectrum. No rate is required of the initial little-o term, and no quantitative nonnegative remainder bound is asserted.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 7, §4, equations (15)-(16): near-pure spectral asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.7–8, (15)–(16): qualitative near-pure asymptotics. No rate is imposed
on the arbitrary initial little-o remainder. Norm exponent 1 is excluded. -/
theorem nearPureNormEntropyAsymptotics {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : ℝ → Matrix I I ℂ) (hrho : ∀ᶠ eps in zeroRight, IsDensityMatrix (rho eps))
    (hnorm : (fun eps => specNorm (rho eps) - (1 - eps)) =o[zeroRight] (fun eps => eps)) :
    (∀ p : ℝ≥0∞, 1 < p →
      (fun eps => pPurity p (rho eps) - (1 - eps)) =o[zeroRight] (fun eps => eps)) ∧
    (fun eps => entropy (rho eps) + eps * Real.log eps) =o[zeroRight]
      (fun eps => eps * Real.log eps) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
