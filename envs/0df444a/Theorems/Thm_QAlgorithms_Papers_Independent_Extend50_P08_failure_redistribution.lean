-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_failure_redistribution
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.failure_redistribution
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:33:41.098097+00:00
-- url     : https://prove2.me/theorems/0fea2c58-0182-4be6-9ce0-ec4714f80ccc
-- title:
--   Redistribute the physical failure effect
-- statement:
--   Let $N\ge1$, $d\ge2$, and let $O$ be a resource filter satisfying $\operatorname{Tr}(O^\dagger O)=d^N$. Suppose $M_0,M_1,\ldots,M_N$ form a physical PSD POVM on Alice’s ports and input. Keeping this resource and Bob’s discard/retain operation, define
--
--   $$\Pi_0=0,\qquad \Pi_i=M_i+\frac1N M_0\quad(1\le i\le N).$$
--
--   The resulting family is a physical POVM with zero failure effect, and its total retained-port map is a quantum channel. This makes the explicit constructive part of (39) precise without invoking the deferred universal scalar fidelity formula (38).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 11, §IV, Eq.(39): constructive redistribution of the physical failure effect

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- §IV, PDF pp.11–12 Eq.(39): constructive redistribution of the physical
failure effect, preserving the resource and the retained-port action. The repeated
Pi_1 label is read as Pi_2, as dictated by the displayed M_i pattern. -/
theorem failure_redistribution (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (O : AliceMatrix d N) (M : Effects d N) (hM : IsPhysicalPBT O M) :
    IsPhysicalPBT O (redistribute M) ∧ redistribute M none = 0 ∧
    (∀ i : Fin N, redistribute M (some i) = M (some i) + ((N : ℝ)⁻¹) • M none) ∧
    IsChannel (successfulMap O (redistribute M)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
