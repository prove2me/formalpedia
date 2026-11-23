-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__star_algebraMap_mem_range_608979362cd4
-- name    : P2M_Formalism_MainNotions_BridgeLemma__star_algebraMap_mem_range_608979362cd4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:36.389468+00:00
-- url     : https://prove2.me/theorems/f750f6d6-5e0f-42d9-9e80-4d48ff2d2f29
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  star algebra Map mem range 608979362cd4: P2 M Formalism Main Notions Bridge Lemma  star algebra Map mem range 608979362cd4
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  star algebra Map mem range 608979362cd4 construction uses the P2 M Formalism Main Notions Bridge Lemma  star algebra Map mem range 608979362cd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
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
open NumberField Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_Formalism_MainNotions_BridgeLemma__star_algebraMap_mem_range_608979362cd4 (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«star_algebraMap_mem_range» := P2M_Formalism_MainNotions_BridgeLemma__star_algebraMap_mem_range_608979362cd4
