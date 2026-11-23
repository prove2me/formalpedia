-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__coords_orthCompanion_be2f4a1d53e6
-- name    : P2M_Formalism_MainNotions_BridgeLemma__coords_orthCompanion_be2f4a1d53e6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:13.864987+00:00
-- url     : https://prove2.me/theorems/6a86ea13-21e4-44e0-bb76-d33116cb54b7
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  coords orth Companion be2f4a1d53e6: P2 M Formalism Main Notions Bridge Lemma  coords orth Companion be2f4a1d53e6
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  coords orth Companion be2f4a1d53e6 construction uses the P2 M Formalism Main Notions Bridge Lemma  coords orth Companion be2f4a1d53e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L125-L127

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
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
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)

theorem P2M_Formalism_MainNotions_BridgeLemma__coords_orthCompanion_be2f4a1d53e6 (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h (e 0) (orthCompanion h e x) = -(star (h (e 1) x)) ∧ h (e 1) (orthCompanion h e x) = star (h (e 0) x) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«coords_orthCompanion» := P2M_Formalism_MainNotions_BridgeLemma__coords_orthCompanion_be2f4a1d53e6
