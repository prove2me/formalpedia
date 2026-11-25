-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_ker_aeval_eta_898fe41a71f0
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncDomain_ker_aeval_eta_898fe41a71f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:29.041199+00:00
-- url     : https://prove2.me/theorems/988ea61d-d3f1-4a02-80ed-af33e1af26e9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Domain ker aeval eta 898fe41a71f0: P2 M Ground Theory Heights  Heights Chart Inc Domain ker aeval eta 898fe41a71f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Domain ker aeval eta 898fe41a71f0 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Domain ker aeval eta 898fe41a71f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L42-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncDomain.lean#L42-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncDomain
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIncDomain_ker_aeval_eta_898fe41a71f0 (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (hI : IsProjPrime I)
    (ht : linForm t ∉ I) :
    have := hI.isPrime
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) :
        MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
      I ⊔ Ideal.span {linForm t - 1} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncDomain».«ker_aeval_eta» := P2M_GroundTheory_Heights__Heights_ChartIncDomain_ker_aeval_eta_898fe41a71f0
