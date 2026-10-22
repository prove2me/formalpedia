-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_localRecoverability
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.localRecoverability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:18:48.806553+00:00
-- url     : https://prove2.me/theorems/d693b338-0875-448e-919e-578c1ef8a595
-- title:
--   §2, (2.1); §3: local recoverability from the multipartite information gap
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   For a state $\rho$ on $A_1A'_1\cdots A_lA'_l$, with $l\ge1$, write
--   $$\Delta(\rho)=I(A_1A'_1:\cdots:A_lA'_l)_\rho-I(A'_1:\cdots:A'_l)_\rho,$$
--   where $I(C_1:\cdots:C_l)=\sum_i H(C_i)-H(C_1\cdots C_l)$.
--
--   There exist local channels $\mathcal R_i:A'_i\to A_iA'_i$ such that
--   $$\Delta(\rho)\ge\left[\frac{1}{2l}\left\|\rho-\left(\bigotimes_{i=1}^l\mathcal R_i\right)(\rho_{A'_1\cdots A'_l})\right\|_1\right]^2.$$
--
--   This quantifies recovery of all unprimed systems from their respective primed systems when the information gap is small.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 4, §2, (2.1); §3: local recoverability from the multipartite information gap

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

/-- PDF p.4,(2.1), proved pp.5–6: local recovery with coefficient 1/(4l^2). -/
theorem localRecoverability {l : ℕ} (hl : 0 < l) {D F : Fin l → Type}
    [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∃ R : (i : Fin l) → Superop (F i) (D i × F i),
      (∀ i, IsChannel (R i)) ∧
      (traceNorm (rho - recover R rho) / (2 * (l : ℝ))) ^ 2 ≤ informationGap rho := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
