-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LatticeBetaCompare_beta_iff__53cf0d0c943c
-- name    : P2M_GlobalTheory_LatticeBetaCompare_beta_iff__53cf0d0c943c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:29:11.839055+00:00
-- url     : https://prove2.me/theorems/5e816d9d-27ad-4286-aae0-5d9c837dac06
-- title:
--   P2 M Global Theory Lattice Beta Compare beta iff  53cf0d0c943c: P2 M Global Theory Lattice Beta Compare beta iff  53cf0d0c943c
-- statement:
--   The P2 M Global Theory Lattice Beta Compare beta iff  53cf0d0c943c construction uses the P2 M Global Theory Lattice Beta Compare beta iff  53cf0d0c943c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L253-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MultAddMultConjugate.lean#L253-L255

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem P2M_GlobalTheory_LatticeBetaCompare_beta_iff__53cf0d0c943c (Λ : Lat E n) (β : c.F) :
    (BetaIs (Dw := Dw) c (toGen Λ) β ∧ BetaAbs (Dw := Dw) c (toGen Λ) β) ↔ IsBeLat Dw c Λ β := by sorry

alias «GlobalTheory».«LatticeBetaCompare».«beta_iff'» := P2M_GlobalTheory_LatticeBetaCompare_beta_iff__53cf0d0c943c
