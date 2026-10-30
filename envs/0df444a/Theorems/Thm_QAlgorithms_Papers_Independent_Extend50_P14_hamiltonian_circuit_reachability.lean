-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_hamiltonian_circuit_reachability
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.hamiltonian_circuit_reachability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:05:41.322396+00:00
-- url     : https://prove2.me/theorems/fa031b12-ff36-43bb-adf9-4ad139ddcb41
-- title:
--   Proposition 3: symmetric local evolution and circuits
-- statement:
--   Fix n≥1 positive-dimensional sites, an on-site representation, and 1≤k≤n. On any finite interval [0,T], let H be an integrable invariant Hermitian Hamiltonian that is a sum of k-local terms, and let V be its absolutely continuous unitary propagator from the identity. Then
--
--   $$V(t)\in V_k\quad(0\le t\le T).$$
--
--   Conversely, every W∈V_k is the endpoint V(1) of a regular propagator with an invariant Hermitian H(t) that is a sum of k-local terms. Symmetry is imposed on the whole Hamiltonian, without imposing it on each original summand.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 14, Proposition 3: local symmetric Hamiltonian evolution equals circuit reachability

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {G : Type*} [Group G] {n : ℕ} {D : Fin n → Type*}

variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [hD : ∀ j, Nonempty (D j)]

-- Positive local dimensions are a physical standing assumption even when unused
-- in the displayed formula; include it in each theorem's elaborated binders.

include hD

/-- PDF pp.14–15, Proposition 3: local summands are not individually assumed
symmetric. The reverse direction uses a regular finite-pulse path on [0,1]. -/
theorem hamiltonian_circuit_reachability (hn : 1 ≤ n) (r : OnSite G D)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∀ (H V : ℝ → Mat (SiteBasis D)) (T : ℝ), Propagator H V T →
      (∀ t ∈ Set.Icc 0 T, CommutesWithAction r.total (H t) ∧ H t ∈ localTermSpan k) →
      ∀ t ∈ Set.Icc 0 T, V t ∈ symmetricLocalGroup r.total k) ∧
    (∀ W ∈ symmetricLocalGroup r.total k, ∃ H V : ℝ → Mat (SiteBasis D),
      Propagator H V 1 ∧ V 1 = W ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, CommutesWithAction r.total (H t) ∧ H t ∈ localTermSpan k) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P14

end
