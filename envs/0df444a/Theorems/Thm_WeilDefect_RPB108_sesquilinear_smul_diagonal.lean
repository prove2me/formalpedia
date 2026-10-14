-- Prove2me | Theorems.Thm_WeilDefect_RPB108_sesquilinear_smul_diagonal
-- name    : WeilDefect.RPB108.sesquilinear_smul_diagonal
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:25:55.506602+00:00
-- url     : https://prove2.me/theorems/95c98f34-1ae7-4558-a52f-c75bb3b78ba2
-- title:
--   Sesquilinear diagonal scalar normalization
-- statement:
--   Let F be an algebraic complex sesquilinear form, conjugate-linear in its first argument and linear in its second. Hermitian means F(u,v)=conj(F(v,u)) for every pair. For a complex module E, z in ℂ and u in E, Re F(zu,zu)=|z|² Re F(u,u). Hermitian symmetry is not needed.
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SesquilinearBlocks.lean#L15-L25; exact native theorem WeilDefect.RPB108.sesquilinear_smul_diagonal. SHA256 4dcb50ec0ebc06cc9c8d402695cb4b59283e9bc0957ac6db754398b8a7683994. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
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

theorem WeilDefect.RPB108.sesquilinear_smul_diagonal {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ) (z : ℂ) (u : E) :
    (F (z • u) (z • u)).re = ‖z‖^2*(F u u).re := by sorry
