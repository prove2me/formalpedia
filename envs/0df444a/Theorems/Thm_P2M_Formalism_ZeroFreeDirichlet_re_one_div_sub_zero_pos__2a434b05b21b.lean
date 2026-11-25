-- Prove2me | Theorems.Thm_P2M_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos__2a434b05b21b
-- name    : P2M_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos__2a434b05b21b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:23.041108+00:00
-- url     : https://prove2.me/theorems/2eb493a4-6327-4c5e-8b11-a06533ae1b90
-- title:
--   P2 M Formalism Zero Free Dirichlet re one div sub zero pos  2a434b05b21b: P2 M Formalism Zero Free Dirichlet re one div sub zero pos  2a434b05b21b
-- statement:
--   The P2 M Formalism Zero Free Dirichlet re one div sub zero pos  2a434b05b21b construction uses the P2 M Formalism Zero Free Dirichlet re one div sub zero pos  2a434b05b21b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealSmallTOf.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RealSmallTOf.lean#L9-L20

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem P2M_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos__2a434b05b21b {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) - ρ)).re := by sorry

alias «Formalism».«ZeroFreeDirichlet».«re_one_div_sub_zero_pos'» := P2M_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos__2a434b05b21b
