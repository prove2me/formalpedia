-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_wirtinger_ne_zero
-- name    : PositivityTheory.Rg.Cz.wirtinger_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:14.989998+00:00
-- url     : https://prove2.me/theorems/7d318c5e-ffa3-5ddd-9e7e-1b5a2d032164
-- title:
--   Cz: wirtinger ne zero
-- statement:
--   The Cz construction uses the wirtinger ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/ArchimedeanWhittakerDerivatives/HasDerivAtOfMulHom.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/ArchimedeanWhittakerDerivatives/HasDerivAtOfMulHom.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtOfContinuousHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WirtingerCombinationNeZero
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_ArchimedeanWhittakerDerivatives_HasDerivAtOfMulHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz

theorem PositivityTheory.Rg.Cz.wirtinger_ne_zero (χ : ℂ → ℂ) (hc : Continuous χ) (hm : ∀ z w, χ (z + w) = χ z * χ w) (hn : ∀ z, ‖χ z‖ = 1)
    (ht : ∃ z, χ z ≠ 1) (D : ℂ → ℂ) (hD : ∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) (β : ℂ) (hβ : β ≠ 0) :
    D β - Complex.I * D (β * Complex.I) ≠ 0 := by sorry
