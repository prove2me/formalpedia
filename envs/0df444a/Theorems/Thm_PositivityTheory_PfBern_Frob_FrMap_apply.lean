-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Frob_FrMap_apply
-- name    : PositivityTheory.PfBern.Frob.FrMap_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:50.510558+00:00
-- url     : https://prove2.me/theorems/d1cf0ff6-8272-4245-b722-e055760232e0
-- title:
--   Frob: Fr Map apply
-- statement:
--   The Frob construction uses the Fr Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/FrobProof.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/FrobProof.lean#L140-L145

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure] [LocallyCompactSpace (Fib p)]
  (μG : Measure G) [μG.IsHaarMeasure] (χ : G →* ℂˣ)

theorem PositivityTheory.PfBern.Frob.FrMap_apply (uG : IsUnimod G) (uH : IsUnimod H) (hχ : Continuous fun g => (χ g : ℂ))
    (α0 : SB G) (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (ξ : eqv X χ)
    (φ : SB (Fib p)) :
    ((FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ : eqvF hp _) : Distr (Fib p)) φ =
      (ξ : Distr X) (fap hp σ hpc μH α0 φ) := by sorry
