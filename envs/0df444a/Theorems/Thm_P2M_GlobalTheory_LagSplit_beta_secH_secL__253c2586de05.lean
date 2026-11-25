-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LagSplit_beta_secH_secL__253c2586de05
-- name    : P2M_GlobalTheory_LagSplit_beta_secH_secL__253c2586de05
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:05.201609+00:00
-- url     : https://prove2.me/theorems/47cc5d0f-abd1-4fe4-8329-a6c1d70141b6
-- title:
--   P2 M Global Theory Lag Split beta sec H sec L  253c2586de05: P2 M Global Theory Lag Split beta sec H sec L  253c2586de05
-- statement:
--   The P2 M Global Theory Lag Split beta sec H sec L  253c2586de05 construction uses the P2 M Global Theory Lag Split beta sec H sec L  253c2586de05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/BetaEqZeroOfCharacter.lean#L193-L198

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}

theorem P2M_GlobalTheory_LagSplit_beta_secH_secL__253c2586de05 {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w = -(2 * I)⁻¹ * (z ⬝ᵥ (imC τ)⁻¹ *ᵥ w) := by sorry

alias «GlobalTheory».«LagSplit».«beta_secH_secL'» := P2M_GlobalTheory_LagSplit_beta_secH_secL__253c2586de05
