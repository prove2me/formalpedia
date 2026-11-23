-- Prove2me | Theorems.Thm_P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646
-- name    : P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:09.146571+00:00
-- url     : https://prove2.me/theorems/0740a018-5a26-4a6c-9616-7412e25267a7
-- title:
--   P2 M Formalism Division Values Local Covolume Basis mem loc P  ad3a70047646: P2 M Formalism Division Values Local Covolume Basis mem loc P  ad3a70047646
-- statement:
--   The P2 M Formalism Division Values Local Covolume Basis mem loc P  ad3a70047646 construction uses the P2 M Formalism Division Values Local Covolume Basis mem loc P  ad3a70047646 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L15-L16

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

theorem P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646 (p : Ideal (𝓞 K)) [p.IsPrime] (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := by sorry

alias «Formalism».«DivisionValues».«LocalCovolumeBasis».«mem_locP'» := P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646
