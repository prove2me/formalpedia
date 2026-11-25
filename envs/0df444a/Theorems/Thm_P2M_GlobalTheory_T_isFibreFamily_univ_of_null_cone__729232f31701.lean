-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isFibreFamily_univ_of_null_cone__729232f31701
-- name    : P2M_GlobalTheory_T_isFibreFamily_univ_of_null_cone__729232f31701
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:28.237457+00:00
-- url     : https://prove2.me/theorems/8e50d7fa-8052-4390-a59e-b284a160a47a
-- title:
--   P2 M Global Theory T is Fibre Family univ of null cone  729232f31701: P2 M Global Theory T is Fibre Family univ of null cone  729232f31701
-- statement:
--   The P2 M Global Theory T is Fibre Family univ of null cone  729232f31701 construction uses the P2 M Global Theory T is Fibre Family univ of null cone  729232f31701 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFibreFamilyUnivOfNullConeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFibreFamilyUnivOfNullConeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFibreFamilyUnivOfNullCone
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFibreFamilyUnivOfNullConeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isFibreFamily_univ_of_null_cone__729232f31701 : ∀ (K V : Type) [NormedField K] [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) (q : V → K), Continuous q → μ {x | q x = 0} = 0 → ∀ (U : Set V) (B : Set K) (fib : K → Measure V), {x | q x ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B → IsFibreFamily μ q id U ν B fib → IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by sorry

alias «GlobalTheory».«T».«isFibreFamily_univ_of_null_cone'» := P2M_GlobalTheory_T_isFibreFamily_univ_of_null_cone__729232f31701
