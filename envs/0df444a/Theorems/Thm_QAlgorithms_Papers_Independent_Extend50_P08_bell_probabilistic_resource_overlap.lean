-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_bell_probabilistic_resource_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.bell_probabilistic_resource_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:30:09.552856+00:00
-- url     : https://prove2.me/theorems/879b2c7e-cb63-4388-a404-2265a93cce9d
-- title:
--   Correctly normalized Bell-resource overlap
-- statement:
--   Let $N\ge1$, $d\ge2$, and $g=(\sum_{\mu\vdash N}m_\mu^2)^{-1}$, with sums over height-bounded physical Schur–Weyl diagrams. Let $O=\sqrt{d^N}\sum_\mu\sqrt{gm_\mu/d_\mu}\,P_\mu$ be the canonical optimal probabilistic filter and let $|\Psi\rangle=(O\otimes I)|\Psi^+\rangle$. This resource is normalized and
--
--   $$|\langle\Psi|\Psi^+\rangle|=\frac{\operatorname{Tr}O}{d^N}=\frac1{\sqrt{d^N}}\sum_{\mu\vdash N}m_\mu\sqrt{g\,d_\mu m_\mu}.$$
--
--   The formula is the source’s proof identity (63). It is deliberately separate from the inconsistent headline formula (61) and qubit formula (62). Here $d_\lambda$ is the dimension of the actual symmetric-group Specht module labelled by $\lambda$, and $m_\lambda$ is its Schur–Weyl multiplicity for local dimension $d$ (with $d=2$ in the qubit case).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 16, Lemma 9 proof, Eq.(63): correctly normalized general resource overlap

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 9 proof, PDF p.16 Eq.(63), with filter (A5), p.20.
This is the correctly normalized proof identity, not the contradictory Eq.(61). -/
theorem bell_probabilistic_resource_overlap (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) :
    IsState (resource (by omega) (probabilisticFilter d N)) ∧
    resourceOverlap (by omega) (probabilisticFilter d N) (1 : AliceMatrix d N) =
      (probabilisticFilter d N).trace.re / (d : ℝ) ^ N ∧
    resourceOverlap (by omega) (probabilisticFilter d N) (1 : AliceMatrix d N) =
      (∑ mu : Schur.Partition d N, pbtSchurMultiplicity mu *
        Real.sqrt (probabilisticNormalization d N * irrepDim mu * pbtSchurMultiplicity mu)) /
        Real.sqrt ((d : ℝ) ^ N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
