-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_kT_nonneg
-- name    : PositivityTheory.Rg.Cz.kT_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:21.543484+00:00
-- url     : https://prove2.me/theorems/faf988e4-4ae4-5f87-85cd-0e5a06497104
-- title:
--   Cz: k T nonneg
-- statement:
--   The Cz construction uses the k T nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L108-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaAbsoluteValues/KugaAbsHolds.lean#L108-L133

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
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem PositivityTheory.Rg.Cz.kT_nonneg {β : Type} [Fintype β] (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P)
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (hB : ∀ x y, B y x = starRingEnd ℂ (B x y))
    (hpos : ∀ x, x ≠ 0 → 0 < (B x x).re) (hTT : ∀ X x y, B (T X x) y = B x (T' X y))
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M) :
    0 ≤ (∑ J : Fin q → β, B (ω (b ∘ J))
      (∑ s, ∑ i, T (b (J s)) (T' (b i) (ω (Function.update (b ∘ J) s (b i)))))).re := by sorry
