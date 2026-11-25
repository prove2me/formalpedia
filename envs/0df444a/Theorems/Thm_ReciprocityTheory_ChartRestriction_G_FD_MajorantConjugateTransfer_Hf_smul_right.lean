-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_smul_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:42.191155+00:00
-- url     : https://prove2.me/theorems/9f6f34d5-e54a-4996-82af-3efc55235388
-- title:
--   Majorant Conjugate Transfer: Hf smul right
-- statement:
--   The Majorant Conjugate Transfer construction uses the Hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantConjugateTransfer.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantConjugateTransfer.lean#L88-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by sorry
