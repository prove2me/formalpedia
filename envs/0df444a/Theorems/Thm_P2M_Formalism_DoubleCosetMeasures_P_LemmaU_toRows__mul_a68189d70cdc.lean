-- Prove2me | Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc
-- name    : P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:52.795795+00:00
-- url     : https://prove2.me/theorems/e0591f73-48fa-4359-acdd-f9b59055ef88
-- title:
--   P2 M Formalism Double Coset Measures P Lemma U to Rows  mul a68189d70cdc: P2 M Formalism Double Coset Measures P Lemma U to Rows  mul a68189d70cdc
-- statement:
--   The P2 M Formalism Double Coset Measures P Lemma U to Rows  mul a68189d70cdc construction uses the P2 M Formalism Double Coset Measures P Lemma U to Rows  mul a68189d70cdc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L25-L28

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}

theorem P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₂ (x * g) = toRows₂ x * g := by sorry

alias «Formalism».«DoubleCosetMeasures».«P».«LemmaU».«toRows₂_mul» := P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc
