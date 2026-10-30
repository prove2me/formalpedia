-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_holevo_partialSwap
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.holevo_partialSwap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:04:11.259436+00:00
-- url     : https://prove2.me/theorems/f4daac83-8751-40fa-878c-b32941306b03
-- title:
--   Unnumbered fixed-port partial-swap Holevo bound (7.11)
-- statement:
--   Let $d\ge1$, $a\in[0,1]$, and let $\sigma$ be a normalized $d$-dimensional state. Let $\mathcal E_{a,\sigma}(X)=\operatorname{Tr}_2(U_a(X\otimes\sigma)U_a^\dagger)$, where $U_a=\sqrt a\,I+i\sqrt{1-a}\,S$ and $S$ swaps the factors. Write $H$ for von Neumann entropy in nats and $\chi$ for the single-use Holevo supremum over all finite normalized mixed-state ensembles. Then
--   $$\chi(\mathcal E_{a,\sigma})\le\log d-(1-a)H(\sigma).$$
--   This is the explicit fixed-port Holevo upper bound obtained from the entropy EPI.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 27, Unnumbered fixed-port partial-swap Holevo bound (7.11)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.27, (7.11): explicit Holevo upper bound for the fixed-port partial swap. -/
theorem holevo_partialSwap {d : ℕ} (hd : 0 < d) (sigma : Mat d)
    (hsigma : IsDensityMatrix sigma) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    holevoNats (fixedPort a sigma) ≤ Real.log (d : ℝ) - (1 - a) * entropy sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
