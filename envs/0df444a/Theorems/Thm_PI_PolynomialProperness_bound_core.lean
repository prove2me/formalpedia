-- Prove2me | Theorems.Thm_PI_PolynomialProperness_bound_core
-- name    : PI.PolynomialProperness.bound_core
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:38:20.451803+00:00
-- url     : https://prove2.me/theorems/fce0073d-e6fe-41ae-ac97-2f1e66b9ae75
-- title:
--   Polynomial Properness: bound core
-- statement:
--   The Polynomial Properness construction uses the bound core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L72-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/AddLeMulPowOfSqLeOfLeMul.lean#L72-L148

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness

theorem PI.PolynomialProperness.bound_core (hG : GVGroup) (hN : NormInv) (hNF : GNFacts)
    {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {Cf Cf' CA Cc : ℝ}
    (hCf : ∀ c b, nsq (fmul k r z c b) ≤ Cf * mx c ^ 2)
    (hCf' : ∀ c b, nsq (fmul k r z' c b) ≤ Cf' * mx c ^ 2)
    (hCc : ∀ s ∈ B.GV k r, ∀ K : ℝ, 0 ≤ K → (∀ i, nsq (s *ᵥ gramVec k r z z' γ i) ≤ K) →
      B.gN s ^ 2 ≤ Cc * (1 + K) ^ 2)
    (σ s' : B.Mat k r) (v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hσ : σ ∈ B.GV k r) (hs' : s' ∈ B.GV k r) (hv : v ∈ UTset (r + 1)) (hu : u' ∈ UTset (r + 1))
    (hσf : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (hsf : ∀ b, s' *ᵥ fvec k r z' b = fmul k r z' u' b)
    (hbv : mx v⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1)))
    (hbu : mx u'⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1))) :
    B.gN σ + B.gN s' ≤ (1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2) *
      B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2) := by sorry
