-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_T2_exists_invariants_iso
-- name    : ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:51.268924+00:00
-- url     : https://prove2.me/theorems/f3855915-87f8-4ebc-baa2-910c9dbb3b76
-- title:
--   T2: exists invariants iso
-- statement:
--   The T2 construction uses the exists invariants iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L346-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean#L346-L353

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable [hT2Core : Fact Core]

theorem ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}
    (hε : IsCyc p K (carry i ε)) :
    ∃ (inv : H2 (twist ε (KO O)) ≃ₗ[O] KO O) (invF : H2 (twist ε (FractionRing O)) ≃ₗ[O] FractionRing O),
      ∀ z, inv (mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε) z) = toKO O (invF z) := by sorry
