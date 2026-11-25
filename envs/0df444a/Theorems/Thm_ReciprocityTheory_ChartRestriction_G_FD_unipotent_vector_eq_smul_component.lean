-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_unipotent_vector_eq_smul_component
-- name    : ReciprocityTheory.ChartRestriction.G.FD.unipotent_vector_eq_smul_component
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:22.69816+00:00
-- url     : https://prove2.me/theorems/f6f87625-d409-502e-97a3-f03cf0e132eb
-- title:
--   FD: unipotent vector eq smul component
-- statement:
--   The FD construction uses the unipotent vector eq smul component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/UnipotentVectorEqSmulComponent.lean#L86-L98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankEqTwoMulHalfDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorEqSmulComponent
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.FD.unipotent_vector_eq_smul_component {r : ℕ} (X : DataX E r) (z0 : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) (K : ℂ)
    (a : X.Ψ → Fin 2 → ℂ) (ha : a τ = ![-(K * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K / (X.NC : ℂ)]) :
    X.uvec ![ξ, (X.NC : E) • x] a τ = K • X.ucomp z0 ξ (X.embV x) τ := by sorry
