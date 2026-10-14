-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_physical_gap_of_sesquilinear_realization
-- name    : WeilDefect.RPB108.DNE27Odd.physical_gap_of_sesquilinear_realization
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:25:53.786521+00:00
-- url     : https://prove2.me/theorems/e52660cc-eca4-4fb4-8757-43305cdee0c5
-- title:
--   DNE27 odd — Physical gap from supplied algebraic form realization
-- statement:
--   Let F be an algebraic complex sesquilinear form, conjugate-linear in its first argument and linear in its second. Hermitian means F(u,v)=conj(F(v,u)) for every pair. Use the unchanged native parity data, k=11/25 and four-column scales. Put X=Σ_i z_i x_i, R=Σ_i z_i σ_i, r=Σ_(i=0)^2 z_(i+1)σ_(i+1), w_i=gramScales_i z_(i+1), and P_a(z)=Σ_i(gramScales_i a_i)z_(i+1). Write Q_M(w)=Σ_ij M_ij Re(conj(w_i)w_j), J=⟨σ_0,Tr⟩, L=lowDiag−Re⟨σ_0,Tσ_0⟩ and U=Q_(V+G/k)(w)−Re⟨r,Tr⟩. Assume the stated operator and four-column norm bounds, all nine native/source matrix enclosures, all three row enclosures, full actual source Gram realization, lowNativeLower≤lowDiag, and high coercivity k‖h‖²≤Re B(h,h). The high form B satisfies subtraction in both arguments and Hermitian symmetry. Weak inverse equations are supplied for R, σ_0 and r. Assume F is Hermitian and its low diagonal, three low-row entries and nine retained entries have the exact stated native realization. At v=h−TR, assume Q(X+v)=Re F(X+v,X+v), column source coupling F(x_i,v)=⟨σ_i,v⟩ and local high restriction Re F(v,v)=Re B(v,v). Then (4/10³⁶)‖Σ_i z_i(x_i−Tσ_i)+h‖²≤Q(Σ_i z_i(x_i−Tσ_i)+h). Both raw and native block identities, covariance symmetry, the finite Schur identity and the Schur floors are derived. F is not required to be bounded on the physical space.
--
--   Parity: odd.
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SesquilinearBlocks.lean#L159-L206; exact native theorem WeilDefect.RPB108.DNE27Odd.physical_gap_of_sesquilinear_realization. SHA256 88f270e58bdb9289a00489833f6e2f41d981c7f840049bbfefba3fcc91337dd9. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27NativePairing_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_DNE27SchurBounds_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.physical_gap_of_sesquilinear_realization {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hFherm : ∀ u v, F u v = star (F v u))
    (Q : E → ℝ) (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hBherm : ∀ u v, B u v = star (B v u))
    (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ))
    (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (z : Fin 4 → ℂ) (h : E) (lowDiag : ℝ)
    (hlow : lowNativeLower ≤ lowDiag)
    (hd : (F (x 0) (x 0)).re = lowDiag)
    (hrow : ∀ i : Fin 3, F (x 0) (x i.succ) = ((gramScales i*a i : ℝ) : ℂ))
    (hret : ∀ i j : Fin 3, F (x i.succ) (x j.succ) =
      ((gramScales i*gramScales j*(V i j+G i j/highFloor) : ℝ) : ℂ))
    (hsolve : ∀ u, B (T (∑ i, z i • source i)) u =
      inner ℂ (∑ i, z i • source i) u)
    (hsolveLow : ∀ u, B (T (source 0)) u = inner ℂ (source 0) u)
    (hsolveRetained : ∀ u, B (T (∑ i : Fin 3, z i.succ • source i.succ)) u =
      inner ℂ (∑ i : Fin 3, z i.succ • source i.succ) u)
    (hQ : Q ((∑ i, z i • x i)+(h-T (∑ i, z i • source i))) =
      (F ((∑ i, z i • x i)+(h-T (∑ i, z i • source i)))
        ((∑ i, z i • x i)+(h-T (∑ i, z i • source i)))).re)
    (hc : ∀ i, F (x i) (h-T (∑ j, z j • source j)) =
      inner ℂ (source i) (h-T (∑ j, z j • source j)))
    (hhighRestriction : (F (h-T (∑ i, z i • source i))
      (h-T (∑ i, z i • source i))).re =
      (B (h-T (∑ i, z i • source i)) (h-T (∑ i, z i • source i))).re)
    (hhigh : highFloor*‖h‖^2 ≤ (B h h).re) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤
      Q ((∑ i, z i • (x i-T (source i)))+h) := by sorry
