-- Prove2me | Theorems.Thm_P2M_Formalism_HC_Landau_natOrder_ne_zero__cbc415af1e91
-- name    : P2M_Formalism_HC_Landau_natOrder_ne_zero__cbc415af1e91
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:17.678555+00:00
-- url     : https://prove2.me/theorems/cad908d4-8c29-462a-97da-fd3805eacdc3
-- title:
--   P2 M Formalism HC Landau nat Order ne zero  cbc415af1e91: P2 M Formalism HC Landau nat Order ne zero  cbc415af1e91
-- statement:
--   The P2 M Formalism HC Landau nat Order ne zero  cbc415af1e91 construction uses the P2 M Formalism HC Landau nat Order ne zero  cbc415af1e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean#L56-L64

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction

theorem P2M_Formalism_HC_Landau_natOrder_ne_zero__cbc415af1e91 {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z y : ℂ} (hy : f y ≠ 0)
    (hz : f z = 0) : analyticOrderNatAt f z ≠ 0 := by sorry

alias «Formalism».«HC».«Landau».«natOrder_ne_zero'» := P2M_Formalism_HC_Landau_natOrder_ne_zero__cbc415af1e91
