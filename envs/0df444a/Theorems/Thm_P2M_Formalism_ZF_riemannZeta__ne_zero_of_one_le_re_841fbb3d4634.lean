-- Prove2me | Theorems.Thm_P2M_Formalism_ZF_riemannZeta__ne_zero_of_one_le_re_841fbb3d4634
-- name    : P2M_Formalism_ZF_riemannZeta__ne_zero_of_one_le_re_841fbb3d4634
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:11.938828+00:00
-- url     : https://prove2.me/theorems/7f405845-ba83-4abf-9b49-02605b56f838
-- title:
--   P2 M Formalism ZF riemann Zeta  ne zero of one le re 841fbb3d4634: P2 M Formalism ZF riemann Zeta  ne zero of one le re 841fbb3d4634
-- statement:
--   The P2 M Formalism ZF riemann Zeta  ne zero of one le re 841fbb3d4634 construction uses the P2 M Formalism ZF riemann Zeta  ne zero of one le re 841fbb3d4634 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/SmallHeightLogDeriv.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/SmallHeightLogDeriv.lean#L17-L24

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_SmallHeightLogDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF

theorem P2M_Formalism_ZF_riemannZeta__ne_zero_of_one_le_re_841fbb3d4634 {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by sorry

alias «Formalism».«ZF».«riemannZeta₁_ne_zero_of_one_le_re» := P2M_Formalism_ZF_riemannZeta__ne_zero_of_one_le_re_841fbb3d4634
