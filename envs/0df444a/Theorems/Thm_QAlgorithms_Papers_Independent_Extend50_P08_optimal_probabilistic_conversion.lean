-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_optimal_probabilistic_conversion
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.optimal_probabilistic_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:27:34.161173+00:00
-- url     : https://prove2.me/theorems/d020ac8b-7fb5-48ef-aea5-02bd0581691d
-- title:
--   Canonical optimal probabilistic-PBT conversion
-- statement:
--   Fix $N\ge1$ and $d\ge2$. Let $g=(\sum_{\mu\vdash N}m_\mu^2)^{-1}$ and $O=\sqrt{d^N}\sum_\mu\sqrt{gm_\mu/d_\mu}\,P_\mu$. On each port, embed the effective success effect from (A5) with coefficients $u_\alpha=d^{N+1}gm_\alpha/(Nd_\alpha)$ on the complementary Young projector and the normalized Bell projector. The physical success effects are $M_i=(O^{-1}\otimes I)E_i(O^{-1}\otimes I)$, and $M_0=I-\sum_iM_i$. This is physical exact pPBT. Redistribute the physical failure by $M_i\mapsto M_i+M_0/N$, keeping the same resource. The resulting deterministic fidelity satisfies
--
--   $$F=p_{\mathrm{succ}}=1-\frac{d^2-1}{N+d^2-1}.$$
--
--   This operational instance uses the source’s explicit canonical data, independently of the ambiguous universal Theorem 4. Here $d_\lambda$ is the dimension of the actual symmetric-group Specht module labelled by $\lambda$, and $m_\lambda$ is its Schur–Weyl multiplicity for local dimension $d$ (with $d=2$ in the qubit case).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 13, Lemma 6: conversion of the canonical optimal pPBT

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 6, PDF p.13 Eq.(48), with the canonical physical realization of
(A5),(A6) on p.20 and redistribution (39) on p.11. The complete effective
normalization is O†O tensor I, rather than identity. -/
theorem optimal_probabilistic_conversion (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) :
    IsPhysicalPBT (probabilisticFilter d N) (probabilisticEffects d N) ∧
    IsExact (probabilisticFilter d N) (probabilisticEffects d N) ∧
    IsPhysicalPBT (probabilisticFilter d N) (redistribute (probabilisticEffects d N)) ∧
    QuditFidelity.entanglementFidelity d (by omega)
      (successfulMap (probabilisticFilter d N) (redistribute (probabilisticEffects d N))) =
        pbtSuccess (probabilisticFilter d N) (probabilisticEffects d N) ∧
    pbtSuccess (probabilisticFilter d N) (probabilisticEffects d N) =
      1 - ((d : ℝ) ^ 2 - 1) / ((N : ℝ) + (d : ℝ) ^ 2 - 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
