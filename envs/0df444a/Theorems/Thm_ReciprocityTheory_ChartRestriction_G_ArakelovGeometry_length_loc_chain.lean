-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_chain
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_chain
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:44.2028+00:00
-- url     : https://prove2.me/theorems/1c85c49d-d31f-4c14-b694-14b44dba59f4
-- title:
--   Arakelov Geometry: length loc chain
-- statement:
--   The Arakelov Geometry construction uses the length loc chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/LengthLocQuotEqZero.lean#L121-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/LengthLocQuotEqZero.lean#L121-L146

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_chain (P : Ideal R) [P.IsPrime] : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal R)
    (f : Fin N → R) (q : Fin N → Ideal R), F (Fin.last N) = ⊤ →
    (∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j, q j ≤ P → q j = P) →
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F 0)) =
      ((∑ j : Fin N, if q j = P then 1 else 0 : ℕ) : ℕ∞)
  := by sorry
