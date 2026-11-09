-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_tree_hamiltonian_gibbs
-- name    : SharpPauliEntanglement.Exact.tree_hamiltonian_gibbs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:37.995761+00:00
-- url     : https://prove2.me/theorems/f898b17d-eed6-48ec-b3cd-73cb65a366de
-- title:
--   Lemma 4.1 — All stabilizer/overlap/sign claims and both Eq. (4.2) identities, including every complex w
-- statement:
--   Let $T$ be any finite tree with at least two vertices. Orient its edges arbitrarily, put qubits $A_e,B_e$ on each edge, let $N=2|E(T)|$, and define $Q_v,H_T$ by (4.1). The $Q_v$ are commuting Hermitian involutions, independent stabilizer generators, and their term-overlap graph is exactly $T$. Every sign assignment $s_v\in\{-1,1\}$ occurs on a nonzero common eigenvector. Moreover,
--
--   $$Z_{H_T}(w)=2^N(\cosh w)^{|V(T)|}\quad(w\in\mathbb C),\qquad \rho_\beta(H_T)=2^{-N}\prod_v(I+\tanh(\beta)Q_v)\quad(\beta\ge0).$$
--
--   Independence is asserted by requiring that no nonempty generator product is any scalar multiple of the identity, as in the source proof. The exact overlap identity and complex partition-function formula support the finite entangled witnesses; a singleton tree is excluded because its construction has empty support.
--
--   Differences from the source:
--   - encoding: arbitrary orientations and N = 2|E| qubits → one ordered representative per undirected edge, a Boolean orientation, and the edge-times-Boolean qubit register; reason: this retains every orientation and exactly two physical qubits per edge; the register cardinality is N
--   - encoding: independent stabilizer generators and occurrence of every sign pattern → Hermitian involutions, commuting pairs, no nonempty scalar product, and a nonzero common eigenvector for each Boolean sign pattern; reason: these spell out the source stabilizer assertion and its proof on p. 19; eigenvectors can be normalized without changing their signs
--   - encoding: finite commuting products → matrix products in a finite enumeration; reason: commutation makes the enumeration irrelevant
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 19, Lemma 4.1

import Definitions.Def_SharpPauliEntanglement_Exact_TreeHamiltonian

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 19, Lemma 4.1, for the actual two-qubits-per-edge construction (4.1).
All complex w, all sign assignments, and both identities (4.2) are included. -/
theorem tree_hamiltonian_gibbs {m : ℕ} (T : SimpleGraph (Fin m)) (hT : T.IsTree)
    (hm : 2 ≤ m) (orientation : TreeEdge T → Bool) :
    (∀ v, (treeGenerator T orientation v).IsHermitian ∧
      treeGenerator T orientation v * treeGenerator T orientation v = 1) ∧
    (∀ v w, Commute (treeGenerator T orientation v) (treeGenerator T orientation w)) ∧
    (∀ U : Finset (Fin m), U.Nonempty → ∀ c : ℂ,
      matrixProduct U (treeGenerator T orientation) ≠ c • 1) ∧
    (∀ v w, T.Adj v w ↔ v ≠ w ∧
      ¬ Disjoint (pauliSupport (treeWord T orientation v))
        (pauliSupport (treeWord T orientation w))) ∧
    (∀ signs : Fin m → Bool,
      ∃ ψ : (TreeQubit T → Bool) → ℂ, ψ ≠ 0 ∧
        ∀ v, (treeGenerator T orientation v).mulVec ψ =
          (if signs v then (-1 : ℂ) else 1) • ψ) ∧
    (∀ w : ℂ, partitionFunction (treeHamiltonian T orientation) w =
      (2 : ℂ) ^ Fintype.card (TreeQubit T) * Complex.cosh w ^ m) ∧
    (∀ β : ℝ, 0 ≤ β → gibbs (treeHamiltonian T orientation) β =
      (((2 : ℂ) ^ Fintype.card (TreeQubit T))⁻¹) •
        matrixProduct Finset.univ (fun v =>
          1 + (Real.tanh β : ℂ) • treeGenerator T orientation v)) := by sorry

end SharpPauliEntanglement.Exact
