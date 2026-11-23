-- Prove2me | Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
-- name    : P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:24.138796+00:00
-- url     : https://prove2.me/theorems/7f9587d9-977b-439e-9d22-c6582dc1f12d
-- title:
--   P2 M Formalism Double Coset Measures P Lemma U to Rows  mul 3f124dd9bb9d: P2 M Formalism Double Coset Measures P Lemma U to Rows  mul 3f124dd9bb9d
-- statement:
--   The P2 M Formalism Double Coset Measures P Lemma U to Rows  mul 3f124dd9bb9d construction uses the P2 M Formalism Double Coset Measures P Lemma U to Rows  mul 3f124dd9bb9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L20-L23

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

theorem P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₁ (x * g) = toRows₁ x * g := by sorry

alias «Formalism».«DoubleCosetMeasures».«P».«LemmaU».«toRows₁_mul» := P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
