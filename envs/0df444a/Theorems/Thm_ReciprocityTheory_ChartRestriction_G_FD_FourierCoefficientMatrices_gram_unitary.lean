-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_gram_unitary
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.gram_unitary
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:33.666691+00:00
-- url     : https://prove2.me/theorems/45e732a5-dcda-4a40-a8d5-ebbd557443cd
-- title:
--   Fourier Coefficient Matrices: gram unitary
-- statement:
--   The Fourier Coefficient Matrices construction uses the gram unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientMatrices.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientMatrices.lean#L231-L238

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

theorem ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.gram_unitary {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n) (τ : X.Ψ)
    (A : Matrix (Fin r) (Fin r) ℂ) : gram τ.1 X.Gm (n τ * A) = gram τ.1 X.Gm A := by sorry
