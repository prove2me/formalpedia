-- Prove2me | Theorems.Thm_P2M_Formalism_HC_Landau_mellin_Gchi__2c78370e3378
-- name    : P2M_Formalism_HC_Landau_mellin_Gchi__2c78370e3378
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:26.188909+00:00
-- url     : https://prove2.me/theorems/c8982c65-6178-47a3-b05a-e63ad23f5f52
-- title:
--   P2 M Formalism HC Landau mellin Gchi  2c78370e3378: P2 M Formalism HC Landau mellin Gchi  2c78370e3378
-- statement:
--   The P2 M Formalism HC Landau mellin Gchi  2c78370e3378 construction uses the P2 M Formalism HC Landau mellin Gchi  2c78370e3378 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean#L322-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean#L322-L345

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
open DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem P2M_Formalism_HC_Landau_mellin_Gchi__2c78370e3378 (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gchi χ x : ℂ) * (x : ℂ) ^ (-s - 1) =
      LSeries (fun n => ((Λ n * (χ n).re : ℝ) : ℂ)) s / (s * (s - 1))
        + (((deriv (LFunction χ) 1 / LFunction χ 1).re : ℝ) : ℂ) * (1 / (s - 1)) := by sorry

alias «Formalism».«HC».«Landau».«mellin_Gchi'» := P2M_Formalism_HC_Landau_mellin_Gchi__2c78370e3378
