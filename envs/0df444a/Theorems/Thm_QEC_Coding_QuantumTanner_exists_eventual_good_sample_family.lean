-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_eventual_good_sample_family
-- name    : QEC.Coding.QuantumTanner.exists_eventual_good_sample_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:02:26.75328+00:00
-- url     : https://prove2.me/theorems/fea3a248-64a4-45f9-8ad4-934c25ae0727
-- title:
--   Quantum Tanner: exists eventual good sample family
-- statement:
--   A single successful local draw works on every supplied cofinal geometric
--   family at the chosen degree. Global distance and rate are proved, not assumed;
--   only the actual spectral and arithmetic-geometric inputs remain conditional.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SpectralFamily.lean#L84-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SpectralFamily.lean#L84-L168

import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
import Definitions.Def_QEC_Coding_QuantumTanner_SpectralFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe u v

theorem QEC.Coding.QuantumTanner.exists_eventual_good_sample_family
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hDeltaHalf : delta < 1 / 2)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho Delta) A B,
        ∀ (Index : Type u) (G : Index → Type v)
          [∀ i, Group (G i)] [∀ i, Fintype (G i)]
          (L : ∀ i, A → G i) (R : ∀ i, B → G i)
          (invA : Equiv.Perm A) (invB : Equiv.Perm B)
          (hL : ∀ i, Function.Injective (L i)) (hR : ∀ i, Function.Injective (R i))
          (hLA : ∀ i a, L i (invA a) = (L i a)⁻¹)
          (hRB : ∀ i b, R i (invB b) = (R i b)⁻¹)
          (hTNC : ∀ i g a b, L i a * g ≠ g * R i b),
        (∀ i, HasMeanZeroBilinearBound
          (cayleySquareComplex (L i) (R i) invA invB (hL i) (hR i) (hLA i) (hRB i)
            (hTNC i)).leftCayleyGraph (2 * Real.sqrt (Delta : ℝ))) →
        (∀ i, HasMeanZeroBilinearBound
          (cayleySquareComplex (L i) (R i) invA invB (hL i) (hR i) (hLA i) (hRB i)
            (hTNC i)).rightCayleyGraph (2 * Real.sqrt (Delta : ℝ))) →
        (∀ N : Nat, ∃ i, N ≤ Fintype.card (G i)) →
        HasGoodSampleFamily L R invA invB hL hR hLA hRB hTNC
          delta epsilon rho Delta sample := by sorry
