-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_raw_block_of_sesquilinear_coupling
-- name    : WeilDefect.RPB108.DNE27Odd.raw_block_of_sesquilinear_coupling
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:25:41.112496+00:00
-- url     : https://prove2.me/theorems/bbd9d9ae-4015-426c-9e37-fb2b5f62b61c
-- title:
--   DNE27 odd — Raw form block from local sesquilinear coupling
-- statement:
--   Let F be an algebraic complex sesquilinear form, conjugate-linear in its first argument and linear in its second. Hermitian means F(u,v)=conj(F(v,u)) for every pair. In a complex inner-product space assume F is Hermitian. For four actual columns x_i,sources σ_i, coordinates z and actual v, put X=Σ_i z_i x_i and R=Σ_i z_i σ_i. Assume Q(X+v)=Re F(X+v,X+v), F(x_i,v)=⟨σ_i,v⟩ for every i, and Re F(v,v)=Re B(v,v). Then Q(X+v)=Re F(X,X)+2 Re⟨R,v⟩+Re B(v,v). Realization and restriction are local at the stated vectors.
--
--   Parity: odd.
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SesquilinearBlocks.lean#L145-L157; exact native theorem WeilDefect.RPB108.DNE27Odd.raw_block_of_sesquilinear_coupling. SHA256 88f270e58bdb9289a00489833f6e2f41d981c7f840049bbfefba3fcc91337dd9. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27SchurBounds_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.raw_block_of_sesquilinear_coupling {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ u v, F u v = star (F v u)) (Q : E → ℝ) (B : E → E → ℂ)
    (x source : Fin 4 → E) (z : Fin 4 → ℂ) (v : E)
    (hQ : Q ((∑ i, z i • x i)+v) =
      (F ((∑ i, z i • x i)+v) ((∑ i, z i • x i)+v)).re)
    (hc : ∀ i, F (x i) v = inner ℂ (source i) v)
    (hhigh : (F v v).re = (B v v).re) :
    Q ((∑ i, z i • x i)+v) = (F (∑ i, z i • x i) (∑ i, z i • x i)).re+
      2*(inner ℂ (∑ i, z i • source i) v).re+(B v v).re := by sorry
