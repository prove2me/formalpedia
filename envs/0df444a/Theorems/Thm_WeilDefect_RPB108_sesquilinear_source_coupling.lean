-- Prove2me | Theorems.Thm_WeilDefect_RPB108_sesquilinear_source_coupling
-- name    : WeilDefect.RPB108.sesquilinear_source_coupling
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:24:46.141951+00:00
-- url     : https://prove2.me/theorems/77fed6e4-6ed8-4d77-aac2-4d4f89a4899e
-- title:
--   Column coupling on an actual high vector
-- statement:
--   Let F be an algebraic complex sesquilinear form, conjugate-linear in its first argument and linear in its second. Hermitian means F(u,v)=conj(F(v,u)) for every pair. In a complex inner-product space, let x_i,σ_i be four actual vectors and v an actual high vector. If F(x_i,v)=⟨σ_i,v⟩ for every column, then for every z in ℂ⁴, F(Σ_i z_i x_i,v)=⟨Σ_i z_i σ_i,v⟩. Coupling is local at v; no global representation is assumed.
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SesquilinearBlocks.lean#L45-L53; exact native theorem WeilDefect.RPB108.sesquilinear_source_coupling. SHA256 4dcb50ec0ebc06cc9c8d402695cb4b59283e9bc0957ac6db754398b8a7683994. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.sesquilinear_source_coupling {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (x source : Fin 4 → E) (z : Fin 4 → ℂ) (v : E)
    (hc : ∀ i, F (x i) v = inner ℂ (source i) v) :
    F (∑ i, z i • x i) v = inner ℂ (∑ i, z i • source i) v := by sorry
