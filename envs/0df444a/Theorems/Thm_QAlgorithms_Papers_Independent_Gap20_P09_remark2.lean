-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_remark2
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.remark2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:21:26.478922+00:00
-- url     : https://prove2.me/theorems/67e08ad7-a5af-4f1c-8514-352b1051e131
-- title:
--   Remark 2: one recovery family simultaneously controls every subset
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   For a state $\rho$ on $A_1A'_1\cdots A_lA'_l$, with $l\ge1$, write
--   $$\Delta(\rho)=I(A_1A'_1:\cdots:A_lA'_l)_\rho-I(A'_1:\cdots:A'_l)_\rho,$$
--   where $I(C_1:\cdots:C_l)=\sum_i H(C_i)-H(C_1\cdots C_l)$.
--
--   There exists one family of local channels $\mathcal R_i:A'_i\to A_iA'_i$ that satisfies the following bound simultaneously for every binary string $j=(j_1,\ldots,j_l)$:
--   $$\Delta(\rho)\ge\left[\frac{\left\|\rho-\left(\bigotimes_i T_i^{j_i}\right)(\rho)\right\|_1}{2w(j)}\right]^2.$$
--   Here $T_i=\mathcal R_i\circ\operatorname{Tr}_{A_i}$, $T_i^0$ is the identity, $T_i^1=T_i$, and $w(j)=\max\{1,\sum_i j_i\}$.
--
--   Thus one recovery family controls all $2^l$ subsets, including the empty subset, whose recovery error is zero.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 6, Remark 2: one recovery family simultaneously controls every subset

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

/-- PDF p.6, Remark 2,(3.13): ONE family controls all 2^l selected subsets. -/
theorem remark2 {l : ℕ} (hl : 0 < l) {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∃ R : (i : Fin l) → Superop (F i) (D i × F i),
      (∀ i, IsChannel (R i)) ∧ ∀ j : Fin l → Bool,
      (traceNorm (rho - subsetRecovery R j rho) /
        (2 * (subsetWeight j : ℝ))) ^ 2 ≤ informationGap rho := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
