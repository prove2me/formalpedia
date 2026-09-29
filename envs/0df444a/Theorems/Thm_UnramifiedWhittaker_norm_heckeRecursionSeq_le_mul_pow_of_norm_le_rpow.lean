-- Prove2me | Theorems.Thm_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
-- name    : UnramifiedWhittaker.norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/9532de9c-0142-5315-9452-c054d815ca43
-- title:
--   Exponential bound for the Hecke recursion sequence
-- statement:
--   Let $q$ and $\kappa$ be real numbers with $1 \le q$ and $0 \le \kappa$, and let $\lambda, \omega \in \mathbb{C}$ satisfy $\|\lambda\| \le q^{\kappa}$ and $\|\omega\| \le q^{\kappa}$, the exponential being the real power $q^{\kappa}$. Let $m$ be a natural number. The sequence `heckeRecursionSeq` attached to a complex parameter $N$ and to $\lambda, \omega$ is defined recursively by $u_0 = 1$, $u_1 = \lambda/N$ and $u_{m+2} = (\lambda u_{m+1} - \omega u_m)/N$; here it is taken with $N$ the image of $q$ in $\mathbb{C}$. The assertion is the bound $$\bigl\| u_m \bigr\| \le (m+1)\,\bigl(2 q^{\kappa}\bigr)^{m}$$ on the $m$-th term of this sequence, with $m$ read as a real number on the right-hand side. No nondegeneracy is assumed beyond $q \ge 1$ (which in particular makes the division by $q$ harmless), and nothing is assumed relating $\lambda$ and $\omega$ beyond the two norm bounds.
--
--   This is the crude growth estimate for the solutions of the Hecke/Satake three-term recursion $q\,u_{m+2} = \lambda u_{m+1} - \omega u_m$ governing the values of an unramified Whittaker function along the torus at a finite place. It is used in the proof of absolute convergence of the finite Rankin–Selberg integral, where it supplies the per-place shell bound cited by [`LanglandsTunnell.RankinSelberg.exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow`](thm.html#LanglandsTunnell.RankinSelberg.exists_summable_forall_tsum_shell_le_exp_of_norm_le_rpow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UnramifiedWhittaker

theorem UnramifiedWhittaker.norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
    (q κ : ℝ) (hq : 1 ≤ q) (hκ : 0 ≤ κ) (lam om : ℂ)
    (hlam : ‖lam‖ ≤ q ^ κ) (hom : ‖om‖ ≤ q ^ κ) (m : ℕ) :
    ‖heckeRecursionSeq (q : ℂ) lam om m‖ ≤ ((m : ℝ) + 1) * (2 * q ^ κ) ^ m := by sorry
