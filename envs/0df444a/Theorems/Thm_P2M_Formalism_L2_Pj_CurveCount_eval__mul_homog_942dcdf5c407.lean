-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Pj_CurveCount_eval__mul_homog_942dcdf5c407
-- name    : P2M_Formalism_L2_Pj_CurveCount_eval__mul_homog_942dcdf5c407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:41.198808+00:00
-- url     : https://prove2.me/theorems/02d7baed-a8ef-4d3e-8c5c-8e41db3991e4
-- title:
--   P2 M Formalism L2 Pj Curve Count eval  mul homog 942dcdf5c407: P2 M Formalism L2 Pj Curve Count eval  mul homog 942dcdf5c407
-- statement:
--   The P2 M Formalism L2 Pj Curve Count eval  mul homog 942dcdf5c407 construction uses the P2 M Formalism L2 Pj Curve Count eval  mul homog 942dcdf5c407 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CurveCountA.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CurveCountA.lean#L7-L16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CurveCountA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CurveCount
open MvPolynomial

theorem P2M_Formalism_L2_Pj_CurveCount_eval__mul_homog_942dcdf5c407 {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (c : S) (g : σ → S)
    {P : MvPolynomial σ R} {k : ℕ} (hP : P.IsHomogeneous k) :
    P.eval₂ f (fun i => c * g i) = c ^ k * P.eval₂ f g := by sorry

alias «Formalism».«L2».«Pj».«CurveCount».«eval₂_mul_homog» := P2M_Formalism_L2_Pj_CurveCount_eval__mul_homog_942dcdf5c407
