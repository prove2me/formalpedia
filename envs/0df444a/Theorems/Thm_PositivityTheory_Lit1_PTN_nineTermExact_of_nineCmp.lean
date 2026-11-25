-- Prove2me | Theorems.Thm_PositivityTheory_Lit1_PTN_nineTermExact_of_nineCmp
-- name    : PositivityTheory.Lit1.PTN.nineTermExact_of_nineCmp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:05.247613+00:00
-- url     : https://prove2.me/theorems/48738fc2-dd56-4f17-b4f6-402cd3cdf05c
-- title:
--   PTN: nine Term Exact of nine Cmp
-- statement:
--   The PTN construction uses the nine Term Exact of nine Cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsTransfer.lean#L50-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsTransfer.lean#L50-L77

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
open PositivityTheory PositivityTheory.Lit1 PositivityTheory.Lit1.PTN
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hρ : ContAction ρ)

theorem PositivityTheory.Lit1.PTN.nineTermExact_of_nineCmp
    (h : NineCmp (loc0 S Av ρ) (tr0 S Av μ j ρ) (loc1 S Av ρ) (tr1 S Av μ j ρ hρ)
      (loc2 S Av ρ) (tr2 S Av μ j ρ)) : NineTermExact S Av μ j ρ hρ := by sorry
