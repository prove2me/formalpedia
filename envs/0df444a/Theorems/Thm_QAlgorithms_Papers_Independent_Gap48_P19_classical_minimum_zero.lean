-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_classical_minimum_zero
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.classical_minimum_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:07:44.442989+00:00
-- url     : https://prove2.me/theorems/5624169f-6a66-4b7f-a248-61acd24b596d
-- title:
--   Classical extension minimum: zero and the fixed-size caveat
-- statement:
--   Let $p_{AB}$ be any probability law on finite nonempty alphabets. Let $\mathcal E(p)$ contain all normalized finite extensions $p_{ABL}$ with marginal $p_{AB}$, allowing every positive auxiliary cardinality. In nats,
--
--   $$\min_{e\in\mathcal E(p)} I_e(A:B\mid L)=0.$$
--
--   The minimum is attained. More generally, any class of valid extensions containing a normalized common-cause extension (5) has attained minimum zero. In contrast, take $A=B$ a fair bit. For the class of all its extensions with a one-element auxiliary alphabet, the attained minimum is $\ln 2>0$.
--
--   This preserves both the unrestricted statement and the source's fixed-cardinality caveat.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 3, §2, Eq.(6), continued on PDF p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3-4, (6): an Eq.(5) member forces a class minimum of zero;
unrestricted auxiliary size always attains zero, whereas size one need not.
Uses the corrected sign of (2), not its printed second line. -/
theorem classical_minimum_zero {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A × B → ℝ) (hp : IsLaw p) :
    IsLeast (classicalScores p) 0 ∧
    (∀ (n : ℕ) (w : Fin n → ℝ) (ka : Fin n → A → ℝ) (kb : Fin n → B → ℝ),
      IsLaw w → IsKernel ka → IsKernel kb →
      ∀ K : Set (ClassicalExtension A B),
        (∀ e ∈ K, ValidClassical p e) → ⟨n, commonCause w ka kb⟩ ∈ K →
        IsLeast {r | ∃ e ∈ K, extensionClassicalCMI e.2 = r} 0) ∧
    (IsLaw fairPair ∧ IsLeast
      {r | ∃ e : ClassicalExtension Bool Bool,
        ValidClassical fairPair e ∧ e.1 = 1 ∧ extensionClassicalCMI e.2 = r}
      (Real.log 2) ∧ 0 < Real.log 2) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
