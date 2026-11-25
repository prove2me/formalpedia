-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kInv_sum
-- name    : PositivityTheory.Rg.Cz.kInv_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:26.02345+00:00
-- url     : https://prove2.me/theorems/de8f0f3f-968b-574f-b3a3-3c99351c58ba
-- title:
--   Cz: k Inv sum
-- statement:
--   The Cz construction uses the k Inv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L24-L25

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz

theorem PositivityTheory.Rg.Cz.kInv_sum : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M), (∀ i j k, c j i k = -c i j k) → (∀ k j, D k (b j) = ∑ i, c i j k • b i) → ∀ {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M), (∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s)))) → ∀ (k : γ) (J : Fin q → β), ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) := by sorry
