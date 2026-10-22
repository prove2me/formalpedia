-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_proposition7
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.proposition7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:25:28.78477+00:00
-- url     : https://prove2.me/theorems/87e80338-7613-49ba-9c01-97735925eb57
-- title:
--   Proposition 7: regularized relative entropy of local recovery is bounded by the gap
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   For a state $\rho$ on $A_1A'_1\cdots A_lA'_l$, with $l\ge1$, write
--   $$\Delta(\rho)=I(A_1A'_1:\cdots:A_lA'_l)_\rho-I(A'_1:\cdots:A'_l)_\rho,$$
--   where $I(C_1:\cdots:C_l)=\sum_i H(C_i)-H(C_1\cdots C_l)$.
--
--   For each integer $n\ge1$, let
--   $$a_n=\min_{\mathcal R_1,\ldots,\mathcal R_l}D_{\rm U}\!\left(\rho^{\otimes n}\,\middle\|\,\left(\bigotimes_i\mathcal R_i\right)(\rho_{A'_1\cdots A'_l}^{\otimes n})\right),$$
--   where $\mathcal R_i:(A'_i)^{\otimes n}\to A_i^{\otimes n}(A'_i)^{\otimes n}$ ranges over all local channels. The Umegaki relative entropy $D_{\rm U}(\alpha\|\beta)=\operatorname{Tr}\alpha(\log\alpha-\log\beta)$ is $+\infty$ if the support of $\alpha$ is not contained in that of $\beta$. The blockwise minima are attained and finite. There exists a finite limit satisfying
--   $$0\le\lim_{n\to\infty}\frac{a_n}{n}\le\Delta(\rho).$$
--
--   The optimization is performed separately at each blocklength. This bounds the regularized relative entropy of local recovery; it does not assert the single-copy conjecture (7.8).
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 18, Proposition 7: regularized relative entropy of local recovery is bounded by the gap

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

-- Exact accepted heterogeneous and selected-register bases; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Gap48.P22
  (ReplicaBasis partyCopyMultiplicity selectedReplicaMarginal)

/-- PDF pp.18–19, Proposition 7,(7.1): attaining blockwise minima and the
actual limit, not just liminf or the performance of one prechosen recovery map.
Blocklengths n+1 avoid division by zero; the limit is unchanged by this shift. -/
theorem proposition7 {l : ℕ} (hl : 0 < l) {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) :
    (∀ n : ℕ, ∃ R : (i : Fin l) →
        Superop (Fin (n+1) → F i) ((Fin (n+1) → D i) × (Fin (n+1) → F i)),
      (∀ i, IsChannel (R i)) ∧
      QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
        (pairedCopies rho (n+1)) (recover R (pairedCopies rho (n+1))) =
        recoveryRelativeEntropy rho (n+1) ∧
      recoveryRelativeEntropy rho (n+1) ≠ ⊤ ∧ recoveryRelativeEntropy rho (n+1) ≠ ⊥) ∧
    ∃ rate : ℝ, 0 ≤ rate ∧ rate ≤ informationGap rho ∧
      Tendsto (fun n : ℕ => (recoveryRelativeEntropy rho (n+1)).toReal / ((n : ℝ)+1))
        atTop (nhds rate) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
