-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_etale_ext
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.etale_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:38.456624+00:00
-- url     : https://prove2.me/theorems/60122a6a-05e0-4c71-8688-0377195df25d
-- title:
--   Chart: etale ext
-- statement:
--   The Chart construction uses the etale ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L130-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean#L130-L151

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ} {S : Type} [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε : S →ₐ[R] R)

theorem ReciprocityTheory.ChartRestriction.G.Chart.etale_ext {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (φ₁ φ₂ : S →ₐ[R] A) (h1 : aug.comp φ₁ = ε) (h2 : aug.comp φ₂ = ε)
    (hs : ∀ j : Fin n, φ₁ (sX (S := S) R j) = φ₂ (sX (S := S) R j)) : φ₁ = φ₂ := by sorry
