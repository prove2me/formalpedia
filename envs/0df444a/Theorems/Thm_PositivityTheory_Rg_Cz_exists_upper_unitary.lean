-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_exists_upper_unitary
-- name    : PositivityTheory.Rg.Cz.exists_upper_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:37.347465+00:00
-- url     : https://prove2.me/theorems/1c3e04e5-1d5c-4d7b-b89e-58f226f13682
-- title:
--   Cz: exists upper unitary
-- statement:
--   The Cz construction uses the exists upper unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/ArchimedeanWhittakerDerivatives/ExistsUpperUnitary.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/ArchimedeanWhittakerDerivatives/ExistsUpperUnitary.lean#L9-L12

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_ArchimedeanWhittakerDerivatives_ExistsUpperUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open Matrix

theorem PositivityTheory.Rg.Cz.exists_upper_unitary {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by sorry
