-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kDel_kD
-- name    : PositivityTheory.Rg.Cz.kDel_kD
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:10.919852+00:00
-- url     : https://prove2.me/theorems/e156d2b3-eea3-52f0-8f5b-442900bde28f
-- title:
--   Cz: k Del k D
-- statement:
--   The Cz construction uses the k Del k D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L18-L19

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_kDel_kD

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

theorem PositivityTheory.Rg.Cz.kDel_kD : ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P), kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) - ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) := by sorry
