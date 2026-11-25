-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_span_L__89e1a95f699d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_span_L__89e1a95f699d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:03.168689+00:00
-- url     : https://prove2.me/theorems/39c04974-34e3-483d-82f4-55c8d40cd178
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Perp Lattice Transfer span L  89e1a95f699d: P2 M Reciprocity Theory Chart Restriction G FD Perp Lattice Transfer span L  89e1a95f699d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Perp Lattice Transfer span L  89e1a95f699d construction uses the P2 M Reciprocity Theory Chart Restriction G FD Perp Lattice Transfer span L  89e1a95f699d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean#L12-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_span_L__89e1a95f699d : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«PerpLatticeTransfer».«span_L'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_span_L__89e1a95f699d
