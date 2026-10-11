-- Prove2me | Theorems.Thm_WeilDefect_RPB108_sesquilinear_gram
-- name    : WeilDefect.RPB108.sesquilinear_gram
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:27:40.822072+00:00
-- url     : https://prove2.me/theorems/c51330c2-c121-4bfa-a324-e6829be33cb4
-- title:
--   Finite sesquilinear Gram realization
-- statement:
--   Let F be an algebraic complex sesquilinear form, conjugate-linear in its first argument and linear in its second. Hermitian means F(u,v)=conj(F(v,u)) for every pair. For a complex module E, three vectors x_i and a real 3×3 matrix M, assume F(x_i,x_j)=M_ij as an equality in ℂ for every pair. For every z in ℂ³, Re F(Σ_i z_i x_i,Σ_i z_i x_i)=Σ_ij M_ij Re(conj(z_i)z_j). No continuity or extra Hermitian assumption is required.
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SesquilinearBlocks.lean#L27-L43; exact native theorem WeilDefect.RPB108.sesquilinear_gram. SHA256 4dcb50ec0ebc06cc9c8d402695cb4b59283e9bc0957ac6db754398b8a7683994. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.sesquilinear_gram {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ) (x : Fin 3 → E)
    (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ i j, F (x i) (x j) = (M i j : ℂ))
    (z : Fin 3 → ℂ) :
    (F (∑ i, z i • x i) (∑ i, z i • x i)).re = complexGram M z := by sorry
