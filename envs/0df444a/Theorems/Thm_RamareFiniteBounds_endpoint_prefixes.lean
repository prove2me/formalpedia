-- Prove2me | Theorems.Thm_RamareFiniteBounds_endpoint_prefixes
-- name    : RamareFiniteBounds.endpoint_prefixes
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T18:47:10.866314+00:00
-- url     : https://prove2.me/theorems/63054f10-f4a0-4ced-8796-a865420184a4
-- title:
--   Exact squarefree-totient majorants at 74 endpoints
-- statement:
--   Let $\varphi(n)$ be Euler's totient and put $D=10^{10}$. Define the integer majorant
--
--   $$
--   w_D(n)=\begin{cases}\lfloor D/\varphi(n)\rfloor+1,&n\text{ squarefree},\\0,&\text{otherwise},\end{cases}
--   \qquad W_D(N)=\sum_{n=1}^{N}w_D(n).
--   $$
--
--   The endpoint table consists of 74 explicit records $(a,b,k,U)$. The interval endpoints run from $(1,1)$ to $(139546,142300)$; $k$ is the exponent used for a power-of-two reduction of the logarithm at $a$, and $U$ is the proposed integer prefix value at $b$.
--
--   For every record in this fixed table, the proposed prefix value is exact:
--
--   $$
--   \forall(a,b,k,U)\text{ in the endpoint table},\qquad W_{10^{10}}(b)=U.
--   $$
--
--   In particular, the final prefix value is $W_{10^{10}}(142300)=131983841862$. The statement certifies all 74 endpoints, including the first endpoint $b=1$.
--
--   This finite arithmetic certificate can be reused independently of a chosen logarithm approximation. Combined with reciprocal rounding, interval coverage, and the endpoint logarithm inequalities, it supplies the computational part of the bound $\sum_{n\le N,\ n\text{ squarefree}}1/\varphi(n)\le\log N+1.4709$ for $1\le N\le142300$.
-- source:
--   Auxiliary integer certificate constructed for the finite verification in O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, Lemma 3.5(1), printed p. 660, equation (3.13). https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The 74-row table and denominator 10^10 are this formal development's certificate data, not a table transcribed from the paper. Target finite-range statement: https://prove2.me/theorems/d69837d9-f165-45c0-a82c-bdb4d2efa4da .

import Definitions.Def_RamareFiniteBounds
set_option autoImplicit false

theorem RamareFiniteBounds.endpoint_prefixes :
    ∀ e ∈ RamareFiniteBounds.logEndpoints,
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper := by sorry
