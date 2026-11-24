-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_lg_chain
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.lg_chain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:48.498976+00:00
-- url     : https://prove2.me/theorems/1a9bd88c-053a-4e6b-8efd-bf588085e431
-- title:
--   Arakelov Geometry: lg chain
-- statement:
--   The Arakelov Geometry construction uses the lg chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L60-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.lg_chain (a : K → ℕ) {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} {q : Fin N → Ideal (MRing ι)} (h0 : IsMultiHomogIdeal (F 0))
    (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    (ha : ∀ j k, c j k ≤ a k) {p : ℕ} (hp : 0 < p) (hpq : ∀ j, (p : MRing ι) ∈ q j) :
    lg (F 0) a = ∑ j, lg (q j) (a - c j) := by sorry
