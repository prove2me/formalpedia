-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/93455fbf-ae56-5215-bd9c-eaadbe13b293
-- title:
--   Residual modularity of level M gives level N when M ∣ N
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a natural number, and let $M, N$ be natural numbers with $N \neq 0$ and $M \mid N$. Suppose $W$ satisfies `W.IsResiduallyModularOfLevel p M`, that is: there are a cusp form $f$ of weight $2$ on $\Gamma_0(M)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ (the ring of algebraic integers) such that $f$ is a normalised eigenform in the sense that its $q$-expansion coefficients (taken with width $1$) satisfy $a_1(f)=1$, $a_{mn}(f)=a_m(f)a_n(f)$ for coprime $m,n$, the recursion $a_{q^{r+2}}(f)=a_q(f)a_{q^{r+1}}(f)-q\,a_{q^{r}}(f)$ for primes $q \nmid M$ and $a_{q^{r+2}}(f)=a_q(f)a_{q^{r+1}}(f)$ for primes $q \mid M$; such that $p \in \mathfrak{m}$; and such that for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M$ and $\ell \neq p$, there is an algebraic integer $a$ whose image in $\mathbb{C}$ is $a_\ell(f)$ and with $a - a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$. Then `W.IsResiduallyModularOfLevel p N` holds, with the same ideal $\mathfrak{m}$.
--
--   This records that the predicate of residual modularity at $p$ is monotone in the level along divisibility, the higher-level eigenform being supplied by oldform transfer from level $M$ to level $N$. It is used when the level in a residual modularity hypothesis must be enlarged before applying the Hecke-local patching-datum constructions of the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_dvd.lean

import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isResiduallyModularOfLevel_of_dvd (W : WeierstrassCurve ℤ) (p : ℕ) {M N : ℕ} [NeZero N] (hMN : M ∣ N) (h : W.IsResiduallyModularOfLevel p M) : W.IsResiduallyModularOfLevel p N := by sorry
