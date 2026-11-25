-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_latDeg_le_of_le
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.latDeg_le_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:02:54.621736+00:00
-- url     : https://prove2.me/theorems/5e28811a-880c-48d6-a1e6-79c4270174bc
-- title:
--   Semi Pt: lat Deg le of le
-- statement:
--   The Semi Pt construction uses the lat Deg le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L152-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L152-L174

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.latDeg_le_of_le {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (C B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hCB : C ≤ B) (hB : B.FG) (hbC : IsKBasisIn C b)
    (hbB : IsKBasisIn B b) : latDeg H C b ≤ latDeg H B b := by sorry
