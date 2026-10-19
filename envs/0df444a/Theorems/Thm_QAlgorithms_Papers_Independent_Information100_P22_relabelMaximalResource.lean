-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_relabelMaximalResource
-- name    : QAlgorithms.Papers.Independent.Information100.P22.relabelMaximalResource
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:50:20.15498+00:00
-- url     : https://prove2.me/theorems/27ea1876-10e7-4f77-b193-995f806db6ad
-- title:
--   Corollary 2: Relabelling of maximally entangled resources
-- statement:
--   Fix one normalized pure maximally entangled resource $R$ on two $\nu$-qubit registers, with $\nu\ge1$. For every factorization $\nu=mk$ with $m\ge2$, $k\ge1$, and every ordered pair of distinct axes, there is a coordinate bijection $e$ satisfying
--   $$e(j,i)=jm+i\qquad(0\le j<k,\ 0\le i<m)$$
--   such that the same resource, expressed in these coordinates, admits exact recovery from each $S_iN$ and perfectly uniform individual concealment. The key is only reindexed, not replaced. This permits several input/output factorizations of one physical resource.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 5, Corollary 2: Relabelling of maximally entangled resources

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Corollary 2, PDF pp.5,24. Resource chosen before every factorization; zero-based Eq.(S15). -/
theorem relabelMaximalResource (nu : ℕ) (hnu : 1 ≤ nu)
    (R : EuclideanSpace ℂ (Qubits nu × Qubits nu)) (hR : IsState R)
    (hmax : traceRight (pureDensity R) = mixed (Qubits nu)) :
    ∀ m k : ℕ, 2 ≤ m → 1 ≤ k → nu = m*k → ∀ P Q : Axis, P ≠ Q →
      ∃ e : Wires m k ≃ Fin nu,
        (∀ w, (e w).val = w.1.val*m+w.2.val) ∧
        AllRecoverable (regroupResource e R) (twoPauliEncoder m k P Q) ∧
        UniformlyConcealed (regroupResource e R) (twoPauliEncoder m k P Q) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
