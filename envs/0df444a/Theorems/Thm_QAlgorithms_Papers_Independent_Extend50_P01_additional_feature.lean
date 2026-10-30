-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_additional_feature
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.additional_feature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:32:48.225081+00:00
-- url     : https://prove2.me/theorems/966c3694-80e1-4cfd-b887-44f08684ee1b
-- title:
--   §II p.5: d+1 commuting features on d qubits
-- statement:
--   Let $d\ge2$, retain all local generators $Z_1,\ldots,Z_d$, and consider unsigned Pauli words that commute with every local $Z_i$ and are invariant under all wire permutations. Among words distinct from identity and all retained generators, the unique possibility is $Z_{\rm all}=\prod_i Z_i$. For the resulting $d+1$-feature exponential embedding, put $C_i=\prod_{j\ne i}\mathrm{CNOT}_{j\to i}$. Then
--   $$C_iZ_iC_i^\dagger=Z_{\rm all},\qquad C_iZ_{\rm all}C_i^\dagger=Z_i,$$
--   while the other local $Z_j$ are fixed. These swaps and wire permutations give an ordinary unitary representation implementing all feature permutations. The embedding is equivariant for that representation.
--
--   **Formalization Note** The source reverses the CNOT controls and targets; the corrected direction above realizes the asserted exchange.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 5, §II p.5: d+1 commuting features on d qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF p.5: additional commuting feature. SOURCE CORRECTION: the printed CNOTs control i
and target all other wires, fixing Z_i. Reversing these controls exchanges Z_i and Z_all. -/
theorem additional_feature (d : ℕ) (hd : 2 ≤ d) :
    (∀ a : Fin d → Fin 4,
      ((∀ i, Commute (pauliWord a) (onWire i pauliZ)) ∧
       (∀ s : Equiv.Perm (Fin d), conjugate (wireMatrix s) (pauliWord a) = pauliWord a) ∧
       pauliWord a ≠ 1 ∧ (∀ i, pauliWord a ≠ onWire i pauliZ)) ↔ a = fun _ => 3) ∧
    (∀ i : Fin d, extraSwap i ∈ Matrix.unitaryGroup (Qubits d) ℂ ∧
      ∀ k : Fin (d + 1), conjugate (extraSwap i) (extraGenerator k) =
        extraGenerator ((Equiv.swap i.castSucc (Fin.last d)) k)) ∧
    (∀ (i : Fin d) (x : Fin (d + 1) → ℝ),
      extraEncoding (featurePullback (Equiv.swap i.castSucc (Fin.last d)) x) =
        conjugate (extraSwap i) (extraEncoding x)) ∧
    (∃ V : Equiv.Perm (Fin (d + 1)) →* Matrix.unitaryGroup (Qubits d) ℂ,
      ∀ s x, extraEncoding (featurePullback s x) = conjugate (V s).val (extraEncoding x)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
