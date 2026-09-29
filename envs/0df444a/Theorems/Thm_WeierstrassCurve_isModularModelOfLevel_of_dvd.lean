-- Prove2me | Theorems.Thm_WeierstrassCurve_isModularModelOfLevel_of_dvd
-- name    : WeierstrassCurve.isModularModelOfLevel_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/168db3e6-a937-512e-b6c3-364f98b9f0b7
-- title:
--   Modularity of an integral model ascends divisible levels
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, and let $M, N$ be natural numbers with $N \neq 0$ and $M \mid N$. The predicate [`WeierstrassCurve.IsModularModelOfLevel`](def/FLTPrelim_Modularity.html#L93) applied to $W$ and a level $L$ asserts the existence of a cusp form $f$ of weight $2$ for $\Gamma_0(L)$ whose $q$-expansion coefficients $a_n(f)$ (the coefficients of `qExpansion 1 f`) satisfy $a_1(f) = 1$, $a_{mn}(f) = a_m(f)a_n(f)$ for coprime $m,n$, the recursion $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f) - p\,a_{p^r}(f)$ for primes $p \nmid L$ and $a_{p^{r+2}}(f) = a_p(f)a_{p^{r+1}}(f)$ for primes $p \mid L$, and which moreover matches $W$ in the sense that for every prime $p$ with $p \nmid \Delta(W)$ and $p \nmid L$ one has $a_p(f) = \operatorname{tr}\mathrm{Frob}_p$ of the reduction of $W$ modulo $p$, as an element of $\mathbb{C}$. The theorem states: if this holds at level $M$, then it holds at level $N$.
--
--   This is the level-raising (oldform) step for the project's notion of modularity of an integral Weierstrass model: the defining condition is imposed only at primes not dividing the level, so it is inherited along divisibility of levels. It is used when passing from a modularity statement at one level to the conductor level, and in the reverse level-lowering bookkeeping for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_of_dvd.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isModularModelOfLevel_of_dvd (W : WeierstrassCurve ℤ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsModularModelOfLevel M) : W.IsModularModelOfLevel N := by sorry
