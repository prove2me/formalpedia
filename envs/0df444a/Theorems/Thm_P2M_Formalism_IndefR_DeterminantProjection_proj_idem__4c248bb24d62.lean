-- Prove2me | Theorems.Thm_P2M_Formalism_IndefR_DeterminantProjection_proj_idem__4c248bb24d62
-- name    : P2M_Formalism_IndefR_DeterminantProjection_proj_idem__4c248bb24d62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:55.391868+00:00
-- url     : https://prove2.me/theorems/c6c2d6e4-ea5e-4181-8600-ad860b85cfba
-- title:
--   P2 M Formalism Indef R Determinant Projection proj idem  4c248bb24d62: P2 M Formalism Indef R Determinant Projection proj idem  4c248bb24d62
-- statement:
--   The P2 M Formalism Indef R Determinant Projection proj idem  4c248bb24d62 construction uses the P2 M Formalism Indef R Determinant Projection proj idem  4c248bb24d62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean#L76-L78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

theorem P2M_Formalism_IndefR_DeterminantProjection_proj_idem__4c248bb24d62 (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) :
    proj σ J u ainv * proj σ J u ainv = proj σ J u ainv := by sorry

alias «Formalism».«IndefR».«DeterminantProjection».«proj_idem'» := P2M_Formalism_IndefR_DeterminantProjection_proj_idem__4c248bb24d62
