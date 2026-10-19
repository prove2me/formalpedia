-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_roundtrip_passesRigidity
-- name    : QAlgorithms.Papers.Independent.Information100.P07.roundtrip_passesRigidity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:40:31.381991+00:00
-- url     : https://prove2.me/theorems/2988bdb5-5654-46da-8e50-ade2d1f40a0b
-- title:
--   Unnumbered: rigidity passes to the given forward and reverse channels
-- statement:
--   Let $\Lambda,\Psi$ be CPTP channels with given finite product Kraus representations $(L_a),(M_b)$. If every $M_bL_a$ is a scalar multiple of a full-space product unitary, then both given channels are mixed LU, each given Kraus operator is a scalar product unitary, and
--   $$\Lambda(I)=\Psi(I)=I.$$
--   There is also a subspace form. If both channels fix the same Schmidt-rank-two pure state, and their composite protects $T=U\otimes\mathbb C^3$, where $U$ is its Alice Schmidt support, then each channel has scaled product-unitary restrictions on $T$, with nonnegative weights summing to one and zero restrictions at zero weights. Both channels fix $P_T$.
--
--   These are properties of the given channels and representations, without asserting finite LOCC implementation. The subspace conclusion also holds with the parties exchanged: T is then C^3 tensor V, where V is the Bob Schmidt plane. A Boolean binder selects the party explicitly.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 11, Unnumbered: rigidity passes to the given forward and reverse channels

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.11–12, Eqs.(S18)–(S19): both given channels inherit rigidity, for either party holding the plane. -/
theorem roundtrip_passesRigidity {m n : ℕ} (A : Fin m → Joint) (B : Fin n → Joint)
    (hA : IsKrausFamily A) (hB : IsKrausFamily B)
    (hpA : ∀ a, IsProduct (A a)) (hpB : ∀ b, IsProduct (B b)) :
    ((∀ b a, ScalarProductUnitary (B b * A a)) →
      MixedLU (krausApply A) ∧ MixedLU (krausApply B) ∧ krausApply A 1 = 1 ∧ krausApply B 1 = 1 ∧
      (∀ a, ScalarProductUnitary (A a)) ∧ (∀ b, ScalarProductUnitary (B b))) ∧
    (∀ (alice : Bool) (psi : Space) (P : Local), IsState psi → (traceRight (pureDensity psi)).rank = 2 →
      P = (if alice then support (traceRight (pureDensity psi)) else support (traceLeft (pureDensity psi))) →
      krausApply A (pureDensity psi) = pureDensity psi →
      krausApply B (pureDensity psi) = pureDensity psi →
      ∀ p : Fin (n * m) → ℝ,
      Protects (fun i => B ((finProdFinEquiv.symm i).1) * A ((finProdFinEquiv.symm i).2))
        (operatorRange (Matrix.kronecker (if alice then P else (1 : Local)) (if alice then (1 : Local) else P))) p →
      (∃ q : Fin m → ℝ, ProductProtects A (if alice then P else 1) (if alice then 1 else P) q) ∧
      (∃ r : Fin n → ℝ, ProductProtects B (if alice then P else 1) (if alice then 1 else P) r) ∧
      krausApply A (Matrix.kronecker (if alice then P else (1 : Local)) (if alice then (1 : Local) else P)) =
        Matrix.kronecker (if alice then P else (1 : Local)) (if alice then (1 : Local) else P) ∧
      krausApply B (Matrix.kronecker (if alice then P else (1 : Local)) (if alice then (1 : Local) else P)) =
        Matrix.kronecker (if alice then P else (1 : Local)) (if alice then (1 : Local) else P)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
