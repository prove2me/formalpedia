-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__lagrange_identity_orthCompanion_f9c10244c23d
-- name    : P2M_Formalism_MainNotions_BridgeLemma__lagrange_identity_orthCompanion_f9c10244c23d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:41.205867+00:00
-- url     : https://prove2.me/theorems/f1c5c1a1-a401-4523-b3ce-29b9143b029e
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  lagrange identity orth Companion f9c10244c23d: P2 M Formalism Main Notions Bridge Lemma  lagrange identity orth Companion f9c10244c23d
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  lagrange identity orth Companion f9c10244c23d construction uses the P2 M Formalism Main Notions Bridge Lemma  lagrange identity orth Companion f9c10244c23d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ExistsSmallMemFractionalIdeal.lean#L143-L149

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

theorem P2M_Formalism_MainNotions_BridgeLemma__lagrange_identity_orthCompanion_f9c10244c23d (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x v v' : V) :
    h (orthCompanion h e x) v * star (h (orthCompanion h e x) v') = h x x * h v' v - h x v * h v' x := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«lagrange_identity_orthCompanion» := P2M_Formalism_MainNotions_BridgeLemma__lagrange_identity_orthCompanion_f9c10244c23d
