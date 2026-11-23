-- Prove2me | Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_weight_one__32b8ae2c834a
-- name    : P2M_Formalism_GM_FrozenVariableComponents_weight_one__32b8ae2c834a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:23.881797+00:00
-- url     : https://prove2.me/theorems/70d0feeb-1df7-4d62-b397-1871b808161c
-- title:
--   P2 M Formalism GM Frozen Variable Components weight one  32b8ae2c834a: P2 M Formalism GM Frozen Variable Components weight one  32b8ae2c834a
-- statement:
--   The P2 M Formalism GM Frozen Variable Components weight one  32b8ae2c834a construction uses the P2 M Formalism GM Frozen Variable Components weight one  32b8ae2c834a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L949-L955
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L949-L955

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K]

theorem P2M_Formalism_GM_FrozenVariableComponents_weight_one__32b8ae2c834a {N r : ℕ} (m : Fin N × Fin r →₀ ℕ) :
    Finsupp.weight (fun _ : Fin N × Fin r => 1) m = ∑ i, ∑ c, m (i, c) := by sorry

alias «Formalism».«GM».«FrozenVariableComponents».«weight_one'» := P2M_Formalism_GM_FrozenVariableComponents_weight_one__32b8ae2c834a
