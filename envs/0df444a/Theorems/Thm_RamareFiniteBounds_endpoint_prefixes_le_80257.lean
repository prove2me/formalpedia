-- Prove2me | Theorems.Thm_RamareFiniteBounds_endpoint_prefixes_le_80257
-- name    : RamareFiniteBounds.endpoint_prefixes_le_80257
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T20:11:37.295879+00:00
-- url     : https://prove2.me/theorems/c140df2f-da25-4e91-a802-01e075139ca3
-- title:
--   Exact squarefree-totient prefixes through 80257
-- statement:
--   Let $\varphi(n)$ be Euler's totient, put $D=10^{10}$, and define
--
--   $$
--   w_D(n)=\begin{cases}\lfloor D/\varphi(n)\rfloor+1,&n\text{ squarefree},\\0,&\text{otherwise},\end{cases}
--   \qquad W_D(N)=\sum_{n=1}^{N}w_D(n).
--   $$
--
--   Let $\mathcal E$ be the fixed public table of 74 records $(a,b,k,U)$. Here $a,b$ are positive interval endpoints, $k$ is an auxiliary nonnegative integer exponent, and $U$ is the specified integer prefix value at $b$. The records cover intervals from $(1,1)$ through $(139546,142300)$. In particular, the table contains $(69862,80257,16,126251687858)$.
--
--   For every record whose upper endpoint is at most 80257, the specified prefix value is exact:
--
--   $$
--   \forall(a,b,k,U)\in\mathcal E,\qquad b\le80257\ \Longrightarrow\ W_D(b)=U.
--   $$
--
--   This assertion covers 69 endpoint records. It includes $W_D(1)=10000000001$ and $W_D(80257)=126251687858$. Together with the continuation statement for larger endpoints, it gives all prefix equalities in the public 74-record certificate for the finite squarefree reciprocal-totient estimate.
-- source:
--   Auxiliary endpoint-range integer certificate constructed in this formal development, supporting the finite verification in O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, Lemma 3.5(1) (statement on printed p. 659), printed p. 660, equation (3.13). https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The 74-row endpoint table, denominator 10^10, cutoff 80257, and exact integer certificate values belong to this formal development; they are not claimed to be printed in Ramaré's paper. Existing public endpoint certificate: https://prove2.me/theorems/63054f10-f4a0-4ced-8796-a865420184a4 . Finite reciprocal-totient target: https://prove2.me/theorems/d69837d9-f165-45c0-a82c-bdb4d2efa4da .

import Definitions.Def_RamareFiniteBounds
set_option autoImplicit false

theorem RamareFiniteBounds.endpoint_prefixes_le_80257  :
    ∀ e ∈ RamareFiniteBounds.logEndpoints, e.hi ≤ 80257 →
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper := by sorry
