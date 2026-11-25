-- Prove2me | Theorems.Thm_UnipMove_GraphH_graph_tau
-- name    : UnipMove.GraphH.graph_tau
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:09.817977+00:00
-- url     : https://prove2.me/theorems/549f1667-dafc-49f4-a369-5a5f9008051d
-- title:
--   Graph H: graph tau
-- statement:
--   The Graph H construction uses the graph tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean#L356-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/BotMulVecExt.lean#L356-L504

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem UnipMove.GraphH.graph_tau {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) (ho : X.IsOrtho x0) (τ : X.Ψ)
    (nτ : Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord) {η z : ℝ} (hη : 0 ≤ η) (hz : 0 ≤ z)
    (hZ1 : X.zN Z1 ≤ z) (hs : η * (1 + z) < 1)
    (hn : ∀ v, X.maj x0 τ ((nτ - 1) *ᵥ v) ≤ η ^ 2 * X.maj x0 τ v) :
    ∃ W : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ,
      Data.opN W ≤ (z + η * (1 + z)) / (1 - η * (1 + z)) ∧
      ∀ Z : X.Coord, Matrix.of (Z τ) = W →
        Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            col (nτ * (mat x0 τ * X.lowBlock Z1 τ)) (Fin.castLE X.p0_le a)) =
          Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le a)) := by sorry
