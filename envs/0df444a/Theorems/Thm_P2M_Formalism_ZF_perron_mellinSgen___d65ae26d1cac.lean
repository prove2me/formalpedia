-- Prove2me | Theorems.Thm_P2M_Formalism_ZF_perron_mellinSgen___d65ae26d1cac
-- name    : P2M_Formalism_ZF_perron_mellinSgen___d65ae26d1cac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:34.860155+00:00
-- url     : https://prove2.me/theorems/d948dcff-eb1b-4859-84ac-04d819a1f58c
-- title:
--   P2 M Formalism ZF perron mellin Sgen   d65ae26d1cac: P2 M Formalism ZF perron mellin Sgen   d65ae26d1cac
-- statement:
--   The P2 M Formalism ZF perron mellin Sgen   d65ae26d1cac construction uses the P2 M Formalism ZF perron mellin Sgen   d65ae26d1cac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L201-L208

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem P2M_Formalism_ZF_perron_mellinSgen___d65ae26d1cac :
    Measurable (Formalism.Sa (fun n => (Λ n : ℝ))) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Formalism.Sa (fun n => (Λ n : ℝ)) x| * x ^ (-σ - 1))
      (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Formalism.Sa (fun n => (Λ n : ℝ)) x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => ((Λ n : ℝ) : ℂ)) s / (s * (s - 1)) := by sorry

alias «Formalism».«ZF».«perron_mellinSgen_Λ» := P2M_Formalism_ZF_perron_mellinSgen___d65ae26d1cac
