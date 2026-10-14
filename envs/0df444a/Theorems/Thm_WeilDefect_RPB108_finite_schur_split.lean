-- Prove2me | Theorems.Thm_WeilDefect_RPB108_finite_schur_split
-- name    : WeilDefect.RPB108.finite_schur_split
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T05:28:21.774547+00:00
-- url     : https://prove2.me/theorems/bcc1bd82-df62-4448-99f7-48e8677a33ca
-- title:
--   Finite Schur split from the native block
-- statement:
--   For continuous complex-linear T, r,v in a complex inner-product space, z,p in ℂ and real N,d,b, assume ⟨v,Tr⟩=conj(⟨r,Tv⟩) and N=d|z|²+2 Re(conj(z)p)+b. Then N−Re⟨zr+v,T(zr+v)⟩=(d−Re⟨r,Tr⟩)|z|²+2 Re(conj(z)(p−⟨r,Tv⟩))+(b−Re⟨v,Tv⟩).
--
--   Exact native statements and definitions are preserved. Constructing the realization attachments for the original Weil form remains unproved future formalization. Complete 1.06 positivity, global continuation and RH are not established.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/FiniteSchur.lean#L33-L46; exact native theorem WeilDefect.RPB108.finite_schur_split. SHA256 110ee29c91511f622c2ea9fee4242f7f9dda9dc25857bf8c0e76a8c9536165b7. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
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

theorem WeilDefect.RPB108.finite_schur_split {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r v : E) (z p : ℂ)
    (N lowDiag retainedNative : ℝ)
    (hherm : inner ℂ v (T r) = star (inner ℂ r (T v)))
    (hnative : N = lowDiag*‖z‖^2+2*(star z*p).re+retainedNative) :
    N-(inner ℂ (z • r+v) (T (z • r+v))).re =
      (lowDiag-(inner ℂ r (T r)).re)*‖z‖^2+
      2*(star z*(p-inner ℂ r (T v))).re+
      (retainedNative-(inner ℂ v (T v)).re) := by sorry
