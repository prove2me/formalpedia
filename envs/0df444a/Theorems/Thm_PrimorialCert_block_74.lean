-- Prove2me | Theorems.Thm_PrimorialCert_block_74
-- name    : PrimorialCert.block_74
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:25:35.617636+00:00
-- url     : https://prove2.me/theorems/496e6c12-da18-4526-bfd1-f35a6c665314
-- title:
--   Primorial certificate block 74 of 75 passes the θ-sieve checker
-- statement:
--   Let $s_1,\dots,s_{11}$ be the 11 records of certificate block 74, the list `ThetaSieve.PrimData74.segs` from the definition `PrimorialCertData_74`. Each record $s_j$ has fields $lo_j, hi_j, L_j, W_j, lo'_j, hi'_j$. The block satisfies three conditions:
--
--   1. Every record passes the sieve checker of `ThetaCertCore`, that is, `Seg.bok` $s_j$ evaluates to `true`.
--   2. Consecutive records connect:
--   $$
--   L_{j+1}=L_j+2W_j,\qquad lo_{j+1}=lo'_j,\qquad hi_{j+1}=hi'_j .
--   $$
--   3. Every record with $L_j+2W_j>16\,000\,001$ satisfies
--   $$
--   hi'_j<(L_j-1)\cdot c,\qquad c=18\,458\,400\,208\,034\,708\,012 .
--   $$
--
--   Here $c=\texttt{LLo}\,68-\texttt{LHi}\,25$ is a fixed-point lower bound for $2^{64}\log(68/25)$, built from the logarithm bounds of `ThetaCertCore`. By the soundness of the checker, a record passing `Seg.bok` carries a bound $lo\le 2^{64}\theta(L-1)\le hi$ to $lo'\le 2^{64}\theta(L+2W-1)\le hi'$, where $\theta(x)=\sum_{p\le x}\log p$. The 75 blocks form a single chain and give $\theta(n)<n\log(68/25)$ for $16\,000\,000<n\le 32\,000\,000$, which is equivalent to the goals `LL_Decomp551a.primorial_c5_*`.
-- source:
--   Computational certificate for the open goals LL_Decomp551a.primorial_c5_lower_first, _lower_second, _upper_first, _upper_second (https://prove2.me/theorems/38410dfa-1944-4a28-b98f-d217484e33c0, https://prove2.me/theorems/ad0251fd-6a65-4ff3-a966-422322ca94df, https://prove2.me/theorems/d1496107-b714-4c70-9749-b225c0dd7c62, https://prove2.me/theorems/4d0d4765-2b88-4d5d-a5cc-2cce65d2d2f4); checker: definition ThetaCertCore.

import Definitions.Def_PrimorialCertData_74

theorem PrimorialCert.block_74 :
    (∀ s ∈ ThetaSieve.PrimData74.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData74.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData74.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) := by sorry
