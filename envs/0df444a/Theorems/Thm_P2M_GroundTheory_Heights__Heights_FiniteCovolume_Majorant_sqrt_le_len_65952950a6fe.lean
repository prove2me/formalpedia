-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_sqrt_le_len_65952950a6fe
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_sqrt_le_len_65952950a6fe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:13.565646+00:00
-- url     : https://prove2.me/theorems/45fcf258-a54f-429d-a8f4-743cd2094f4f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant sqrt le len 65952950a6fe: P2 M Ground Theory Heights  Heights Finite Covolume Majorant sqrt le len 65952950a6fe
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant sqrt le len 65952950a6fe construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant sqrt le len 65952950a6fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenCauchySchwarz.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenCauchySchwarz.lean#L62-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenCauchySchwarz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_sqrt_le_len_65952950a6fe {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    Real.sqrt (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re ≤ M.len y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«Majorant».«sqrt_le_len» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_sqrt_le_len_65952950a6fe
