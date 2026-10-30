-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_optimal_resources_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.optimal_resources_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:28:18.098316+00:00
-- url     : https://prove2.me/theorems/9b1e5807-cf8c-4a75-90e8-6babdcc0e6e0
-- title:
--   Overlap of the canonical optimal resources
-- statement:
--   For $N\ge1$ and $d\ge2$, let $P_\mu$ be the physical Schur–Weyl isotypic projectors, with Specht dimensions $d_\mu$ and multiplicities $m_\mu$. Let $v$ be any nonnegative unit principal eigenvector of the actual height-truncated teleportation matrix. Define $g=(\sum_\mu m_\mu^2)^{-1}$, $O=\sqrt{d^N}\sum_\mu\sqrt{gm_\mu/d_\mu}\,P_\mu$, and $\widetilde O=\sqrt{d^N}\sum_\mu v_\mu P_\mu/\sqrt{d_\mu m_\mu}$. The vectors $|\Psi\rangle=(O\otimes I)|\Psi^+\rangle$ and $|\widetilde\Psi\rangle=(\widetilde O\otimes I)|\Psi^+\rangle$ are normalized and their root fidelity is
--
--   $$|\langle\Psi|\widetilde\Psi\rangle|=\frac{\sum_\mu v_\mu m_\mu}{\sqrt{\sum_\nu m_\nu^2}}.$$
--
--   This compares the specified positive central-filter resources, rather than arbitrary states attaining the same performance.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 14, Lemma 7: overlap of optimal probabilistic and deterministic resources

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 7, PDF pp.14–15 Eq.(51): root fidelity of the two specific
normalized filtered Bell resources, with numerator v_mu m_mu. -/
theorem optimal_resources_overlap (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (v : Schur.Partition d N → ℝ) (hv : IsPrincipal v) :
    IsState (resource (by omega) (probabilisticFilter d N)) ∧
    IsState (resource (by omega) (deterministicFilter v)) ∧
    resourceOverlap (by omega) (probabilisticFilter d N) (deterministicFilter v) =
      (∑ mu : Schur.Partition d N, v mu * pbtSchurMultiplicity mu) /
        Real.sqrt (∑ nu : Schur.Partition d N, (pbtSchurMultiplicity nu) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
