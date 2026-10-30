-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_side_information_separation
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.side_information_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:13:34.221027+00:00
-- url     : https://prove2.me/theorems/6850939f-a73b-4fe5-b974-ec116dd76f6a
-- title:
--   An achievable separation when side information may change
-- statement:
--   For $0<t<1/2$, let $p=(1/2-t,1/2-t,2t)$ and $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$. The original two-qubit ensemble consists of $|00\rangle,|10\rangle,|++\rangle$ with probabilities $p$, and is irreducible. A controlled-NOT with $A$ as control maps these letters exactly to $|00\rangle,|11\rangle,|++\rangle$, preserving each $A$ pure density and changing the side register to $C'$. Write $S$ for the binary von Neumann entropies of the corresponding ensemble averages and set
--   $$q_{\rm original}(t)=\tfrac12(S(A)+S(AC)-S(C)),\quad q_{\rm modified}(t)=\tfrac12(S(A)+S(AC')-S(C')).$$
--   The original preserved-side-information optimum is $q_{\rm original}(t)$ and is attained with its Theorem 3 entanglement corner. There are codes preserving the modified side information with quantum rate $q_{\rm modified}(t)$, hence a protocol at that rate when the original side information need not be preserved. Furthermore,
--   $$\lim_{t\to0^+}q_{\rm original}(t)=1,\qquad\lim_{t\to0^+}q_{\rm modified}(t)=\tfrac12.$$
--
--   This gives an achievable separation, without claiming optimality of the modified-side-information rate or irreducibility at $t=0$.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 5, Discussion: explicit CNOT example

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Explicit separation example, PDF p.5: CNOT preserves A letter by letter,
the preserved-side-information optimum tends to 1, and a rate tending to 1/2
is achievable when C may be replaced by Cprime. The printed final S(A|C)
is read as S(A|Cprime), as required by the preceding paragraph. Neither
optimality of the relaxed rate nor irreducibility at t=0 is asserted. -/
theorem side_information_separation :
    (∀ t : Set.Ioo (0 : ℝ) (1 / 2),
      (exampleOriginal t).Valid ∧ (exampleModified t).Valid ∧
      (exampleOriginal t).Irreducible ∧
      (∀ x, act cnot ((exampleOriginal t).joint x) = (exampleModified t).joint x) ∧
      (∀ x, pureDensity ((exampleOriginal t).psi x) =
        pureDensity ((exampleModified t).psi x)) ∧
      (exampleOriginal t).quantumCorner = exampleOriginalRate t.val ∧
      (exampleOriginal t).OptimalQuantumCorner (exampleOriginalRate t.val)
        (exampleOriginal t).entanglementCorner ∧
      (∃ P : QuantumCodeSequence Bool Bool,
        Tendsto (fun n => (P n).fidelity (exampleModified t)) atTop (nhds 1) ∧
        Tendsto (fun n => (P n).quantumRate) atTop (nhds (exampleModifiedRate t.val)))) ∧
    Tendsto exampleOriginalRate (nhdsWithin 0 (Set.Ioo 0 (1 / 2))) (nhds 1) ∧
    Tendsto exampleModifiedRate (nhdsWithin 0 (Set.Ioo 0 (1 / 2))) (nhds (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
