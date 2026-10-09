-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumLB_hankel_succ_posSemidef
-- name    : SymPolyOpt.PowerSumLB.hankel_succ_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:15.867337+00:00
-- url     : https://prove2.me/theorems/31dcd8f0-3ead-4bd0-bd80-11259329083c
-- title:
--   Proof of Theorem 6.6(b), p. 26 — H_n(s) ⪰ 0 implies H_{r+1}(s) ⪰ 0 for r < n
-- statement:
--   Let $s = (s_0, s_1, \dots)$ be a real sequence and $r + 1 \le n$. The Hankel matrix $H_{r+1}(s)$ is the leading $(r+1)\times(r+1)$ principal block of
--   $$H_n(s) = \begin{pmatrix} H_{r+1}(s) & U(s) \\ U(s)^T & V(s) \end{pmatrix},$$
--   hence
--   $$H_n(s) \succeq 0 \implies H_{r+1}(s) \succeq 0.$$
--
--   This is the first step of the proof of Theorem 6.6(b): it passes from the $n \times n$ constraint of (6.5) to a small Hankel matrix containing the objective entry $s_{2r}$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 26, proof of Theorem 6.6(b), "Therefore, H_n(s) ⪰ 0 implies H_{r+1}(s) ⪰ 0"

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

namespace SymPolyOpt.PowerSumLB

/-- H_{r+1}(s) is a leading principal submatrix of H_n(s) when r + 1 ≤ n, so it inherits
positive semidefiniteness. -/
theorem hankel_succ_posSemidef (n : ℕ) :
    ∀ (s : ℕ → ℝ) (r : ℕ), r + 1 ≤ n → (hankel n s).PosSemidef →
      (hankel (r + 1) s).PosSemidef := by sorry

end SymPolyOpt.PowerSumLB
