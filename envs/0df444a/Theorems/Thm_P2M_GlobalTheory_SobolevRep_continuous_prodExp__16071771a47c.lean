-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SobolevRep_continuous_prodExp__16071771a47c
-- name    : P2M_GlobalTheory_SobolevRep_continuous_prodExp__16071771a47c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:31:18.553658+00:00
-- url     : https://prove2.me/theorems/9cdd77ef-33c2-4a5e-88da-278df72a54bd
-- title:
--   P2 M Global Theory Sobolev Rep continuous prod Exp  16071771a47c: P2 M Global Theory Sobolev Rep continuous prod Exp  16071771a47c
-- statement:
--   The P2 M Global Theory Sobolev Rep continuous prod Exp  16071771a47c construction uses the P2 M Global Theory Sobolev Rep continuous prod Exp  16071771a47c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSobolevRepresentationProdExp.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSobolevRepresentationProdExp.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory
open GlobalTheory.SobolevRep
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem P2M_GlobalTheory_SobolevRep_continuous_prodExp__16071771a47c {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by sorry

alias «GlobalTheory».«SobolevRep».«continuous_prodExp'» := P2M_GlobalTheory_SobolevRep_continuous_prodExp__16071771a47c
