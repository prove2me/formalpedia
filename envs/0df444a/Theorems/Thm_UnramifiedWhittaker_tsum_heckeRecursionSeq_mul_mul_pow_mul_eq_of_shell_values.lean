-- Prove2me | Theorems.Thm_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values
-- name    : UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/0ac03b4b-06f4-5bac-97dc-c7bb7ee6271a
-- title:
--   Closed form for a shell-valued Hecke generating series
-- statement:
--   Let $N,\lambda,\omega,y,c,w$ be complex numbers, $k$ a natural number and $I:\mathbb{N}\to\mathbb{C}$ a sequence. Write $u_m=$ `heckeRecursionSeq N lam om m` for the sequence determined by $u_0=1$, $u_1=\lambda/N$ and $u_{m+2}=(\lambda u_{m+1}-\omega u_m)/N$, all divisions taken in $\mathbb{C}$ (so with the convention $x/0=0$ when $N=0$). Assume that $I_m=0$ for every $m<k$, that $I_k=c\,w$, that $I_m=w$ for every $m>k$, and that the family $m\mapsto u_m y^m$ is summable. Then
--   $$\Bigl(\sum_{m\ge 0} u_m I_m y^m\Bigr)\bigl(1-\tfrac{\lambda}{N}y+\tfrac{\omega}{N}y^2\bigr)=w\Bigl(c\,u_k y^k+\bigl(u_{k+1}-c\,\tfrac{\lambda}{N}u_k\bigr)y^{k+1}+(c-1)\tfrac{\omega}{N}u_k y^{k+2}\Bigr).$$
--   No hypothesis is imposed on $N$, $\lambda$, $\omega$, $c$, $w$ or $y$ beyond the summability of $m\mapsto u_m y^m$; in particular $N=0$ is permitted.
--
--   This is the elementary generating-series identity underlying the evaluation of an unramified Whittaker integral along the torus, where the coefficients $u_m$ satisfy the three-term Hecke recursion attached to a pair $(\lambda,\omega)$ with residue parameter $N$, and the factor $I$ records the values of a unit-shell integral: zero below the level $k$, a transitional value $c\,w$ at $k$, and the constant $w$ above it. It is used in the construction of the cuspidal synthesis step of the converse-theorem argument, via [`LanglandsTunnell.Converse.CuspSynthesis.exists_isHaarMeasure_torusTransform_eq_of_isJLNice`](thm.html#LanglandsTunnell.Converse.CuspSynthesis.exists_isHaarMeasure_torusTransform_eq_of_isJLNice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UnramifiedWhittaker

theorem UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values
    (N lam om y c w : ℂ) (k : ℕ) (I : ℕ → ℂ)
    (hI0 : ∀ m, m < k → I m = 0) (hIk : I k = c * w) (hI1 : ∀ m, k < m → I m = w)
    (hy : Summable fun m : ℕ => heckeRecursionSeq N lam om m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * I m * y ^ m) * (1 - lam / N * y + om / N * y ^ 2) =
      w * (c * heckeRecursionSeq N lam om k * y ^ k +
        (heckeRecursionSeq N lam om (k + 1) - c * (lam / N) * heckeRecursionSeq N lam om k) *
          y ^ (k + 1) +
        (c - 1) * (om / N) * heckeRecursionSeq N lam om k * y ^ (k + 2)) := by sorry
