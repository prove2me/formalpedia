-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_capacities_commonPositiveLimit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.capacities_commonPositiveLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:31:34.131922+00:00
-- url     : https://prove2.me/theorems/0df2dca7-ac19-4c01-ac14-54c2985c5c66
-- title:
--   Figure 3 caption, unnumbered: common nonzero high-acceleration and large-cloner capacity limit
-- statement:
--   The cloning capacities and the qubit-input Unruh capacities have the same positive limiting value. More precisely, there exists a real number $L>0$ such that
--
--   $$
--   \lim_{\ell\to\infty}C(\mathrm{Cl}_{1,\ell-1})=L
--   =\lim_{z\to1^-}C(U_z),\qquad 0\le z<1.
--   $$
--
--   Both capacities are defined by positive-block-length regularized Holevo optimization before taking these limits. The source does not give a closed form for $L$, and none is added. This is a common nonzero asymptotic capacity claim, without a monotonicity assertion or a channel value at the singular endpoint.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 6, Figure 3 caption

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P49

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Support50.P01
  (unruhSectorDilation unruhWeight unruhBlockDilation unruhBlockWeight
   unruhReceiver unruhReceiverEntropy)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.QuditFidelity (depolarizingMap)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Figure 3 caption: the two capacities approach the same positive
limit. The z limit is from below and does not define a channel at z=1. -/
theorem capacities_commonPositiveLimit :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun k : ℕ => classicalCapacityBits (cloner k)) atTop (nhds L) ∧
      Tendsto unruhClassicalCapacity (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds L) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
