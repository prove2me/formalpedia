-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_Hf_sub_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_sub_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:44.43535+00:00
-- url     : https://prove2.me/theorems/819ec39a-9a9d-4756-9855-1452406a028b
-- title:
--   Majorant Conjugate Transfer: Hf sub right
-- statement:
--   The Majorant Conjugate Transfer construction uses the Hf sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantConjugateTransfer.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantConjugateTransfer.lean#L83-L86

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_sub_right (x : Frame X.Ψ r) (τ : X.Ψ) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w - w') = X.Hf x τ u w - X.Hf x τ u w' := by sorry
