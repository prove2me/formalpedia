-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_wwDeg_sub_eq_llDeg_86a1dd3df16e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_wwDeg_sub_eq_llDeg_86a1dd3df16e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:16.530894+00:00
-- url     : https://prove2.me/theorems/2cad896b-bb39-4079-913a-d3dbc4530042
-- title:
--   P2 M Ground Theory Heights  Heights Inter ww Deg sub eq ll Deg 86a1dd3df16e: P2 M Ground Theory Heights  Heights Inter ww Deg sub eq ll Deg 86a1dd3df16e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ww Deg sub eq ll Deg 86a1dd3df16e construction uses the P2 M Ground Theory Heights  Heights Inter ww Deg sub eq ll Deg 86a1dd3df16e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreProduct.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreProduct.lean#L36-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_wwDeg_sub_eq_llDeg_86a1dd3df16e (n : ℕ) :
    (fun k => (T.wwDeg n 1 k : ℤ) - (T.wwDeg (n + 3) 0 k : ℤ)) = T.llDeg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«wwDeg_sub_eq_llDeg» := P2M_GroundTheory_Heights__Heights_Inter_wwDeg_sub_eq_llDeg_86a1dd3df16e
