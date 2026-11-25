-- Prove2me | Theorems.Thm_P2M_Formalism_ZeroFreeDirichlet_inRegion_mono__5281f592e2e7
-- name    : P2M_Formalism_ZeroFreeDirichlet_inRegion_mono__5281f592e2e7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:07.921843+00:00
-- url     : https://prove2.me/theorems/3e8852b7-b1d2-4ba3-9a63-a789283c5ebb
-- title:
--   P2 M Formalism Zero Free Dirichlet in Region mono  5281f592e2e7: P2 M Formalism Zero Free Dirichlet in Region mono  5281f592e2e7
-- statement:
--   The P2 M Formalism Zero Free Dirichlet in Region mono  5281f592e2e7 construction uses the P2 M Formalism Zero Free Dirichlet in Region mono  5281f592e2e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZFRDirichletOf.lean#L21-L26

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
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

theorem P2M_Formalism_ZeroFreeDirichlet_inRegion_mono__5281f592e2e7 {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by sorry

alias «Formalism».«ZeroFreeDirichlet».«inRegion_mono'» := P2M_Formalism_ZeroFreeDirichlet_inRegion_mono__5281f592e2e7
