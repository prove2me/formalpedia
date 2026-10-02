-- Prove2me | Theorems.Thm_SennottDP_ChainASM_upper_hessenberg_excess_to_N_conforming
-- name    : SennottDP.ChainASM.upper_hessenberg_excess_to_N_conforming
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:04:59.40111+00:00
-- url     : https://prove2.me/theorems/44b52338-faf5-4644-9249-68a36a89b570
-- title:
--   Corollary C.5.4 — for an upper Hessenberg 0 standard chain, the ATAS sending excess probability to N is conforming
-- statement:
--   Let $\Gamma$ be a $0$ standard Markov chain with costs on $S=\{0,1,2,\dots\}$ whose transition matrix is upper Hessenberg:
--   $$P_{ij}=0\qquad\text{for } i\ge 2 \text{ and } j<i-1,$$
--   so the chain moves down at most one state at a time. Assume that $S_N=\{0,1,\dots,N\}$ for $N\ge 1$ and that the ATAS sends the excess probability to $N$, i.e. $q_N(i,r,N)=1$ for $i\in S_N$, $r\notin S_N$. Then the ATAS is conforming.
--
--   This covers the common truncation of a queue at buffer size $N$ in which arrivals that would overflow the buffer are placed in the top state $N$.
--
--   **Formalization Note** The AS is indexed from $N_0\ge 1$, with $S_N=\{0,\dots,N\}$ for all $N\ge N_0$. "Sends the excess probability to $N$" is $q_N(i,r,N)=1$, which forces $q_j(i,r,N)=0$ for $j\ne N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 314, Corollary C.5.4

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem upper_hessenberg_excess_to_N_conforming
    (Γ : MC ℕ) (hz : Γ.IsZStandard 0)
    (hHess : ∀ i j : ℕ, 2 ≤ i → j + 1 < i → Γ.P i j = 0)
    (AS : ApproxSeq Γ) (hN₀ : 1 ≤ AS.N₀)
    (hSN : ∀ N, AS.N₀ ≤ N → AS.SN N = Finset.range (N + 1))
    (q : ℕ → ℕ → ℕ → ℕ → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N → q N i r N = 1) :
    AS.IsConforming 0 := by sorry

end SennottDP.ChainASM
