-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__card_submodules_quotient_le_89e4f83fcf5a
-- name    : P2M_Formalism_MainNotions_BridgeLemma__card_submodules_quotient_le_89e4f83fcf5a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:39.671773+00:00
-- url     : https://prove2.me/theorems/b0ca4a7a-8262-4d5e-97b9-f730c0138d9e
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  card submodules quotient le 89e4f83fcf5a: P2 M Formalism Main Notions Bridge Lemma  card submodules quotient le 89e4f83fcf5a
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  card submodules quotient le 89e4f83fcf5a construction uses the P2 M Formalism Main Notions Bridge Lemma  card submodules quotient le 89e4f83fcf5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L63-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L63-L88

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
variable (K : Type) [Field K] [NumberField K]

theorem P2M_Formalism_MainNotions_BridgeLemma__card_submodules_quotient_le_89e4f83fcf5a (d : 𝓞 K) (hd : d ≠ 0) :
    Finite (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)) ∧
    Nat.card (Submodule (𝓞 K) ((Fin 2 → 𝓞 K) ⧸ scaledFreeModule K d)) ≤ ((Algebra.norm ℤ d).natAbs ^ 2) ^ 2 := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«card_submodules_quotient_le» := P2M_Formalism_MainNotions_BridgeLemma__card_submodules_quotient_le_89e4f83fcf5a
