-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_native_block_of_sesquilinear_entries
-- name    : WeilDefect.RPB108.DNE27Even.native_block_of_sesquilinear_entries
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:25:33.151874+00:00
-- url     : https://prove2.me/theorems/06f8afa9-b9ad-41a3-86e0-acf6dc04f338
-- title:
--   DNE27 even — Native block from actual sesquilinear entries
-- statement:
--   Let F be an algebraic complex sesquilinear form, conjugate-linear in its first argument and linear in its second. Hermitian means F(u,v)=conj(F(v,u)) for every pair. Use the unchanged native parity data, k=11/25 and four-column scales. Put X=Σ_i z_i x_i, R=Σ_i z_i σ_i, r=Σ_(i=0)^2 z_(i+1)σ_(i+1), w_i=gramScales_i z_(i+1), and P_a(z)=Σ_i(gramScales_i a_i)z_(i+1). Write Q_M(w)=Σ_ij M_ij Re(conj(w_i)w_j), J=⟨σ_0,Tr⟩, L=lowDiag−Re⟨σ_0,Tσ_0⟩ and U=Q_(V+G/k)(w)−Re⟨r,Tr⟩. In a complex inner-product space assume F is Hermitian, Re F(x_0,x_0)=lowDiag, F(x_0,x_(i+1))=gramScales_i a_i, and F(x_(i+1),x_(j+1))=gramScales_i gramScales_j(V_ij+G_ij/k) for all retained entries, as exact complex equalities. Then Re F(X,X)=lowDiag|z_0|²+2 Re(conj(z_0)P_a(z))+Q_(V+G/k)(w). No interval or norm assumptions are needed for this identity.
--
--   Parity: even.
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SesquilinearBlocks.lean#L9-L40; exact native theorem WeilDefect.RPB108.DNE27Even.native_block_of_sesquilinear_entries. SHA256 88f270e58bdb9289a00489833f6e2f41d981c7f840049bbfefba3fcc91337dd9. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
import Definitions.Def_RPB108_DNE27SchurBounds_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.native_block_of_sesquilinear_entries {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ u v, F u v = star (F v u)) (x : Fin 4 → E)
    (V G : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℝ) (lowDiag : ℝ)
    (hd : (F (x 0) (x 0)).re = lowDiag)
    (hrow : ∀ i : Fin 3, F (x 0) (x i.succ) = ((gramScales i*a i : ℝ) : ℂ))
    (hret : ∀ i j : Fin 3, F (x i.succ) (x j.succ) =
      ((gramScales i*gramScales j*(V i j+G i j/highFloor) : ℝ) : ℂ))
    (z : Fin 4 → ℂ) :
    (F (∑ i, z i • x i) (∑ i, z i • x i)).re =
      lowDiag*‖z 0‖^2+2*(star (z 0)*nativePairing a z).re+retainedNativeEnergy V G z := by sorry
