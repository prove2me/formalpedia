-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_supermaps_noncausal
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.supermaps_noncausal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:28:07.618036+00:00
-- url     : https://prove2.me/theorems/b9b14672-ca21-4160-92c4-5fe8dfdcda3d
-- title:
--   State-labelled deterministic effects witness supermap noncausality
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. For a channel system $(A_0,A_1)$, a deterministic effect is operationally a deterministic one-comb: prepare a joint density matrix with finite memory, insert the input map, and discard the output and memory. These effects are exactly the functionals
--
--   $$u_\rho(E)=\operatorname{Re}\operatorname{Tr}[E(\rho)],\qquad \rho\in\mathcal D(A_0).$$
--
--   Equality here is equality of the real functional on all complex-linear maps. If $\dim A_0\geq2$, there exist density matrices $\rho,\sigma$ and a CPTNI event $E$ with $u_\rho(E)\ne u_\sigma(E)$, witnessing noncausality. Moreover, for any nonzero finite $B_0,B_1$ and entangled density matrix $\tau$ on $A_0B_0$, $u_\tau$ cannot agree on all bipartite CPTNI events with $u_{\rho\otimes\sigma}$ for any density matrices $\rho,\sigma$. Entanglement means failure to belong to the finite convex hull of product density matrices. These statements compare effects on probabilistic events, where their difference is observable.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 22, Example F.6; p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.5,21–22, Example F.6: deterministic effects are state-labelled
feed-and-discard circuits; input dimension at least two gives distinct effects on events.
Entangled input states give nonfactorizing effects. -/
theorem supermaps_noncausal [Nonempty A1] [Nonempty B0] [Nonempty B1] [Nontrivial A0] :
    (∀ f : QMap A0 A1 → ℝ, IsDeterministicTester f ↔
      ∃ rho : Op A0, IsDensityMatrix rho ∧ f = discardEffect rho) ∧
    (∃ rho sigma : Op A0, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      ∃ E : QMap A0 A1, IsCPTNI E ∧ discardEffect rho E ≠ discardEffect sigma E) ∧
    (∀ tau : Op (A0 × B0), IsDensityMatrix tau → ¬ Entanglement.IsSeparableDensity tau →
      ¬ ∃ rho : Op A0, ∃ sigma : Op B0, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
        ∀ E : QMap (A0 × B0) (A1 × B1), IsCPTNI E →
          discardEffect tau E = discardEffect (Matrix.kronecker rho sigma) E) := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
