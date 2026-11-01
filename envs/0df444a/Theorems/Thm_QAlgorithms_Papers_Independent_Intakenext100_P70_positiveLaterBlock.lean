-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_positiveLaterBlock
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.positiveLaterBlock
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:44:50.526628+00:00
-- url     : https://prove2.me/theorems/216b2ef3-6f53-42ea-b5ef-3a0ec37fa1ee
-- title:
--   A later block has positive coherent information
-- statement:
--   Let $0<p<1$ and $0<\kappa<1/2$. There exist positive integers $N,m,r$, an integer $d\geq2$, and a weight $q$ that can be chosen with
--   $$
--   q=\frac13,\qquad r=2m+\lceil\log_2m\rceil,\qquad d=2Nr.
--   $$
--   Construct $\Gamma$ from the normalized Choi state (S18), and $\mathcal M$ from the measured, retained switch (S15), with whole-register erasure flags as defined on pp.5–6. These choices satisfy the PPT condition
--   $$
--   0<q\leq\frac13,\qquad \left(\frac d{d-1}\right)^{rN}\leq\frac{1-q}{q},
--   $$
--   so $\Gamma$ is PPT-binding; $\mathcal M$ is completely positive and trace preserving. They also give
--   $$
--   Q^{(N+1)}(\mathcal M)>0,
--   $$
--   where the rate divides the maximum coherent information over all joint density inputs by $N+1$ and is measured in bits.
--
--   This existential construction makes the finite-block obstruction compatible with positive capacity.
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 9, Supplementary Lemma 4; parameter choice p.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Supplementary Lemma 4, PDF pp.9--10: choose actual S18 parameters satisfying S19
and giving positive optimized coherent information at N+1 uses. The witness choices
q=1/3, d=2*N*r and integer r are the choices used by the proof. -/
theorem positiveLaterBlock (p kappa : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hk0 : 0 < kappa) (hk1 : kappa < 1 / 2) :
    ∃ P : CubittParameters, CubittValid P ∧ P.q = 1 / 3 ∧ P.r = cubittRepetitions P.m ∧
      P.d = 2 * P.N * P.r ∧ CubittPPTCondition P ∧ CubittPPTBinding (cubittGammaChannel P) ∧
      IsChannel (cubittPaperChannel P kappa p) ∧
      0 < cubittBlockInformation (cubittPaperChannel P kappa p) (P.N + 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
