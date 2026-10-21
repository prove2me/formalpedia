-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_rank_one_refinement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.rank_one_refinement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:19:34.062485+00:00
-- url     : https://prove2.me/theorems/0d5214c8-c16e-4096-a4a8-250c8740866e
-- title:
--   Rank-one physical refinement with no loss increase
-- statement:
--   Let $d\ge1$, let positive nonzero covariant seeds $\Pi_i$ have total trace $d$, and let an admissible finite-loss dual reconstruct the operation, channel or unital target span. There is a finite refined family $E_j=\alpha_j|\Psi_j\rangle\!\rangle\langle\!\langle\Psi_j|$, with $\alpha_j>0$ and $\|\Psi_j\|_{\rm HS}=1$, and a parent-label map $p$, such that
--
--   $$\Pi_i=\sum_{j:p(j)=i}E_j,\qquad\sum_j\operatorname{Tr}E_j=d,\qquad\eta_{\rm refined}\le\eta_{\rm original}.$$
--
--   The refined family has a physical covariant tester and an unbiased finite-loss dual on the same target. Discarding the refined label gives the original statistics. This existence and loss comparison justify restricting the seed optimization to rank one; rank one is not an extra hypothesis on the original experiment.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, Paragraph after (32)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, paragraph after (32): physical rank-one refinement with coarse-graining,
normalization and no loss increase, rather than a rank-one assumption on original seeds. -/
theorem rank_one_refinement {d : ℕ} (hd : 0 < d) (K : TomographyDomain)
    {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar)
    (P : J → Op (ChoiBasis d)) (D : J × GroupPair d → Op (ChoiBasis d))
    (hP : Seeds P)
    (hD : TomographyAdmissible (Measure.count.prod (haar.prod haar)) (covariant P) D K) :
    ∃ (n : ℕ) (parent : Fin n → J) (E : Fin n → Op (ChoiBasis d))
      (F : Fin n × GroupPair d → Op (ChoiBasis d)),
      Seeds E ∧ (∀ j, RankOneSeed (E j)) ∧
      (∀ i, ∑ j ∈ Finset.univ.filter (fun j => parent j = i), E j = P i) ∧
      TomographyAdmissible (Measure.count.prod (haar.prod haar)) (covariant E) F K ∧
      eta K (Measure.count.prod (haar.prod haar)) (covariant E) F ≤
        eta K (Measure.count.prod (haar.prod haar)) (covariant P) D := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
