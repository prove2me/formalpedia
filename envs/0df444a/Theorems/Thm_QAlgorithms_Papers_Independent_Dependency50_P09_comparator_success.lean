-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_comparator_success
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.comparator_success
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:00:38.137509+00:00
-- url     : https://prove2.me/theorems/abe68212-f8a9-4fb8-9b0d-e51138d10785
-- title:
--   Proposition 18 (Bound for comparator test success probability)
-- statement:
--   Let $M:A\to B'$ be CP with $\beta(M)\le1$, where $\widehat A,A,B'$ have common positive dimension $d$. Put $\Phi_c=d^{-1}\sum_i|ii\rangle\langle ii|$ and $\Pi=\sum_i|ii\rangle\langle ii|$. Here $\Phi_c$ is mixed and classically correlated.
--
--   $$
--   \operatorname{Tr}[\Pi(\operatorname{id}_{\widehat A}\otimes M)(\Phi_c)]\le\frac1d.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 11, Proposition 18 (Bound for comparator test success probability)

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

/-- Proposition 18 (Bound for comparator test success probability), arXiv:2010.01058v3, PDF pp.11.
 -/
theorem comparator_success {I : Type} [Fintype I] [Nonempty I]
    (M : Superop I I) (hM : CP M) (hbeta : bipartiteBeta (pointMap M) ≤ 1) :
    (comparator * idTensorSuperop M (classicalPhi I)).trace.re ≤
      (Fintype.card I : ℝ)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
