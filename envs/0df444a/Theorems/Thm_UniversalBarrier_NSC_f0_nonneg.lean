-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_f0_nonneg
-- name    : UniversalBarrier.NSC.f0_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:38.490018+00:00
-- url     : https://prove2.me/theorems/d0eb8bfc-af87-4e16-b5d1-b95dd1a576fc
-- title:
--   §4.1.7, pp. 12–13 — f₀(γ) ≥ 0 for γ ≥ 1 (inequality (23))
-- statement:
--   Let $k\ge2$ be an integer and $\gamma\ge1$. Then
--   $$f_0(\gamma)=k(\gamma^k-1)\bigl[k(k+1)(\gamma^{k+2}-1)-2k(k+2)(\gamma^{k+1}-1)+(k+1)(k+2)(\gamma^k-1)\bigr]-(k+1)\bigl[k(\gamma^{k+1}-1)-(k+1)(\gamma^k-1)\bigr]^2\ \ge\ 0.$$
--
--   This is the algebraic inequality (23) cleared of denominators; it completes the proof of inequality (11), the equivalent form of Proposition 1's inequality (5).
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, pp. 12–13, §4.1.7, inequality (23) and the definition of f0

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

namespace UniversalBarrier.NSC

theorem f0_nonneg (k : ℕ) (hk : 2 ≤ k) (γ : ℝ) (hγ : 1 ≤ γ) : 0 ≤ f0 k γ := by sorry

end UniversalBarrier.NSC
