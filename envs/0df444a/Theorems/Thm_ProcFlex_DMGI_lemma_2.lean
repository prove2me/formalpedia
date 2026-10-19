-- Prove2me | Theorems.Thm_ProcFlex_DMGI_lemma_2
-- name    : ProcFlex.DMGI.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:25.173548+00:00
-- url     : https://prove2.me/theorems/f828a030-b988-4541-9701-c165e1230cca
-- title:
--   Lemma 2: exact DMGI of the alternate long chain
-- statement:
--   Consider $2k$ unit-capacity plants and $2k$ products, with $k$ products at each positive margin $P_L<P_H$, and an alternate long chain $\mathrm{AL}$. For a feasible count vector $K=(k_{10},k_{20},k_{21})$, set $k_{22}=k-k_{20}-k_{21}$ and $k_{11}=k-k_{10}$. The homogeneous DMGI is
--
--   $$
--   \delta^K(\mathrm{AL})=\begin{cases}
--   2k_{22}P_H+2k_{21}P_L,&k_{20}=0,\\
--   2k_{22}P_H+(2k-2k_{22}-\min(k_{10},k_{20}+1)-\min(k_{10},k_{20}-1))P_L,&1\le k_{20}<k,\\
--   2k_{11}P_L,&k_{20}=k.
--   \end{cases}
--   $$
--
--   This exact value is the benchmark for every other balanced long-chain arrangement.
--
--   **Formalization Note** The homogeneous program (5) is (4) at $\mu=0$ and $C_j=1$. Feasible $K\in Q$ makes natural-number differences in the count definitions exact; the middle coefficient is computed in real arithmetic.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 22, Lemma 2 and (6)

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Lemma 2 and equation (6), p. 22: the three exact cases of the homogeneous
DMGI for an alternate long chain. -/
theorem lemma_2 (k : ℕ) (hk : 1 ≤ k)
    (S : System (2 * k) (2 * k) 2) (hS : S.IsValid)
    (hC : ∀ j, S.C j = 1) (hcard : (S.s 1).card = k)
    (πAL : Equiv.Perm (Fin (2 * k))) (hAL : IsAlternate S πAL)
    (K : Fin 2 → Fin 3 → ℕ) (hK : InQ S K) :
    let k10 : ℕ := K 0 0
    let k20 : ℕ := K 1 0
    let k21 : ℕ := K 1 1
    let k22 : ℕ := k - k20 - k21
    let k11 : ℕ := k - k10
    dmgi S 0 K (longChain πAL) =
      if k20 = 0 then
        2 * (k22 : ℝ) * S.P 1 + 2 * (k21 : ℝ) * S.P 0
      else if k20 = k then
        2 * (k11 : ℝ) * S.P 0
      else
        2 * (k22 : ℝ) * S.P 1 +
          (((2 * k : ℕ) : ℝ) - 2 * (k22 : ℝ) -
            (min k10 (k20 + 1) : ℝ) -
            (min k10 (k20 - 1) : ℝ)) * S.P 0 := by sorry

end ProcFlex.DMGI
