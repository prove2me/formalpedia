-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_kBasisIn_single
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.kBasisIn_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:09.886477+00:00
-- url     : https://prove2.me/theorems/554ca8da-314e-44d4-af23-a365fff53d77
-- title:
--   Semi Pt: k Basis In single
-- statement:
--   The Semi Pt construction uses the k Basis In single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegR.lean#L55-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegR.lean#L55-L69

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.kBasisIn_single {K : Type} [Field K] [NumberField K] {r : ℕ} (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hat : ∀ x ∈ Gr, IsAt i x) (v : Fin r → K)
    (hv : v ∈ Gr) (hvi : v i ≠ 0) : IsKBasisIn Gr ![v] := by sorry
