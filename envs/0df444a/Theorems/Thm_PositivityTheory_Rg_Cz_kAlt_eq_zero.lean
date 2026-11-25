-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kAlt_eq_zero
-- name    : PositivityTheory.Rg.Cz.kAlt_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:31.534355+00:00
-- url     : https://prove2.me/theorems/4aa0ebb0-b9b9-5861-b981-c6b103f906a9
-- title:
--   Cz: k Alt eq zero
-- statement:
--   The Cz construction uses the k Alt eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L27-L28

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

theorem PositivityTheory.Rg.Cz.kAlt_eq_zero : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M] {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ → ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by sorry
