-- Prove2me | Theorems.Thm_SennottDP_ChainASM_atas_structural_conforming
-- name    : SennottDP.ChainASM.atas_structural_conforming
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:00:54.091987+00:00
-- url     : https://prove2.me/theorems/9bc82674-81e7-4edc-9c21-18b31e5f8468
-- title:
--   Proposition C.5.3 — an ATAS whose augmentation distributions do not increase m_·z and c_·z is conforming
-- statement:
--   Let $\Gamma$ be a $z$ standard Markov chain with costs on a denumerable state space $S$. Assume that there are an ATAS $(\Gamma_N)$ with augmentation distributions $q_j(i,r,N)$ and a nonnegative integer $N^*$ such that
--   $$\sum_{j\in S_N-\{z\}}q_j(i,r,N)\,m_{jz}\le m_{rz},\qquad i\in S_N,\ r\notin S_N,\ N\ge N^*,$$
--   and
--   $$\sum_{j\in S_N-\{z\}}q_j(i,r,N)\,c_{jz}\le c_{rz},\qquad i\in S_N,\ r\notin S_N,\ N\ge N^*.$$
--   Then the ATAS is conforming.
--
--   The conditions say that redistributing the probability of leaving $S_N$ never increases the expected time or cost to reach $z$, compared with the state $r$ that was actually targeted; it is a structural condition that can be checked from the first passage moments of $\Gamma$ alone.
--
--   **Formalization Note** The page prints the index set of the sums as $S_n-\{z\}$; it is read as $S_N-\{z\}$. The conditions are imposed for $N\ge\max(N^*,N_0)$, where the ATAS is defined.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 312, Proposition C.5.3, (C.37)–(C.38)

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem atas_structural_conforming {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q) (Nstar : ℕ)
    (h37 : ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * Γ.meanPassage {z} j ≤ Γ.meanPassage {z} r)
    (h38 : ∀ N, Nstar ≤ N → AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ r, r ∉ AS.SN N →
      ∑ j ∈ (AS.SN N).filter (· ≠ z), q N i r j * Γ.passageCost {z} j ≤ Γ.passageCost {z} r) :
    AS.IsConforming z := by sorry

end SennottDP.ChainASM
