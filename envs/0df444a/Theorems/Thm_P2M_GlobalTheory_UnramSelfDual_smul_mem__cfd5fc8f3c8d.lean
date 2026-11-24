-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d
-- name    : P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:32.645091+00:00
-- url     : https://prove2.me/theorems/e72ff239-a872-4142-9f6b-ddc69d78b29c
-- title:
--   P2 M Global Theory Unram Self Dual smul mem  cfd5fc8f3c8d: P2 M Global Theory Unram Self Dual smul mem  cfd5fc8f3c8d
-- statement:
--   The P2 M Global Theory Unram Self Dual smul mem  cfd5fc8f3c8d construction uses the P2 M Global Theory Unram Self Dual smul mem  cfd5fc8f3c8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L141-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}

theorem P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d {a : A} (ha : a ∈ O) {y : Fin M → A} (hy : y ∈ L) : a • y ∈ L := by sorry

alias «GlobalTheory».«UnramSelfDual».«smul_mem'» := P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d
