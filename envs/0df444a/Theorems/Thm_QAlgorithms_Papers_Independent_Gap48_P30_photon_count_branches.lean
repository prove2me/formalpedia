-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_photon_count_branches
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.photon_count_branches
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:22:29.332989+00:00
-- url     : https://prove2.me/theorems/1ba8747d-5549-4b97-acc7-b03d688013b5
-- title:
--   Appendix 5d: exact photon-count branch law and conditional Fock output
-- statement:
--   Let $k\ge0$, $0\le\lambda<1$, and $0\le T\le1$. Bob mixes his half of $|\Psi_\lambda^{(k)}\rangle$ with a vacuum ancillary mode on a splitter of transmissivity $T$ and counts the reflected photons. For outcome $l\ge0$, write $v_l=(I\otimes L_l)|\Psi_\lambda^{(k)}\rangle$, where $L_l$ is the actual vacuum-loss Kraus operator. Then
--
--   $$
--   P(l)=\|v_l\|^2=(1-T)^l\lambda^{2l}\binom{k+l}{l}\frac{(1-\lambda^2)^{k+1}}{(1-T\lambda^2)^{k+l+1}},\qquad
--   v_l=\sqrt{P(l)}\,|\Psi_{\sqrt T\lambda}^{(k+l)}\rangle.
--   $$
--
--   The probabilities are nonnegative and sum to one; the complete splitter Kraus family has a strongly convergent normalization sum and its tensors realize the physical matrices. The unnormalized identity applies also when $P(l)=0$.
--
--   This gives both the exact branch law and the conditional Fock output used in the deterministic protocol. Direct splitter coefficients cover $T=0,1$ without the intermediate division by $T$ in the printed derivation. Explicitly, at $T=1$, only $l=0$ occurs and its branch is the unchanged input. At $T=0$, $P(l)=p_l^{(k)}(\lambda)$ and $v_l=\sqrt{p_l^{(k)}(\lambda)}\,|k+l,0\rangle$.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 10, Appendix 5d, (A.60)–(A.65)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF p.10, (A.60)-(A.65). Bob's exact photon-count
probability and unnormalized conditional vector, including both splitter
endpoints via the direct Kraus coefficients. Zero probability branches carry
no assertion of a normalized conditional vector. -/
theorem photon_count_branches (k : ℕ) (lambda T : ℝ)
    (hl : 0 ≤ lambda) (hlu : lambda < 1) (hT : 0 ≤ T) (hTu : T ≤ 1) :
    D.AttenuatorRealized (Real.sqrt T) ∧
    D.KrausComplete (D.attenuatorKraus (Real.sqrt T)) ∧
    ProbabilityLaw (countProbability k lambda T) ∧
    (∀ ell : ℕ, TensorRealized 1 (D.attenuatorKraus (Real.sqrt T) ell) ∧
      ‖countBranch k lambda T ell‖ ^ 2 = countProbability k lambda T ell ∧
      countBranch k lambda T ell =
        (Real.sqrt (countProbability k lambda T ell) : ℂ) •
          squeezed (k + ell) (Real.sqrt T * lambda)) ∧
    (T = 1 → ∀ ell : ℕ,
      countProbability k lambda T ell = (if ell = 0 then 1 else 0) ∧
      countBranch k lambda T ell = (if ell = 0 then squeezed k lambda else 0)) ∧
    (T = 0 → ∀ ell : ℕ,
      countProbability k lambda T ell = fockSchmidtWeight k lambda ell ∧
      countBranch k lambda T ell =
        (Real.sqrt (fockSchmidtWeight k lambda ell) : ℂ) • D.bipartiteKet (k + ell, 0)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
