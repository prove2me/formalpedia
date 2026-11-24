-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:04.590252+00:00
-- url     : https://prove2.me/theorems/1d4749d9-bd5c-4c2c-b07b-3f17e7c4c2f5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog mul 0a86f7155eda: P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog mul 0a86f7155eda
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog mul 0a86f7155eda construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Gen SESStep is Multi Homog mul 0a86f7155eda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGenSESStep.lean#L19-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda {p q : MRingOver S ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GenSESStep».«isMultiHomog_mul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_isMultiHomog_mul_0a86f7155eda
