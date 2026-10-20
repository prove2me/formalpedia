-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_geometric_channel_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.geometric_channel_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:11:58.218548+00:00
-- url     : https://prove2.me/theorems/172b9247-7059-4fba-8454-446994f7f852
-- title:
--   Lemma 35
-- statement:
--   Let $N$ be a finite-dimensional CPTP channel and $M$ any CP map on the same ports, including zero. Channel divergences include every finite reference and normalized input. Use the extended real topology and approach one from both sides through positive orders different from one.
--
--   $$
--   \lim_{\alpha\to1}\widehat D_\alpha(N\Vert M)=\widehat D(N\Vert M).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 28, Lemma 35

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Lemma 35, arXiv:2010.01058v3, PDF pp.28.
 -/
theorem geometric_channel_limit {I : Type} [Fintype I] [Nonempty I]
    {J : Type} [Fintype J] [Nonempty J]
    (N M : Superop I J) (hN : IsChannel N) (hM : CP M) :
    Tendsto (fun alpha : ℝ => channelD (geometricD alpha) N M) orderOne
      (𝓝 (channelD bsD N M)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
