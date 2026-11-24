-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_G_Inhab_map_colSpan__20236f61806d
-- name    : P2M_Formalism_MainNotions_G_Inhab_map_colSpan__20236f61806d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:58.612985+00:00
-- url     : https://prove2.me/theorems/42970063-29aa-42c4-b17f-2aca25410e79
-- title:
--   P2 M Formalism Main Notions G Inhab map col Span  20236f61806d: P2 M Formalism Main Notions G Inhab map col Span  20236f61806d
-- statement:
--   The P2 M Formalism Main Notions G Inhab map col Span  20236f61806d construction uses the P2 M Formalism Main Notions G Inhab map col Span  20236f61806d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L79-L83

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}

theorem P2M_Formalism_MainNotions_G_Inhab_map_colSpan__20236f61806d (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by sorry

alias «Formalism».«MainNotions».«G».«Inhab».«map_colSpan'» := P2M_Formalism_MainNotions_G_Inhab_map_colSpan__20236f61806d
