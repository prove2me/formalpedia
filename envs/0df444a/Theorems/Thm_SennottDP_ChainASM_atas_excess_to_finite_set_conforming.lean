-- Prove2me | Theorems.Thm_SennottDP_ChainASM_atas_excess_to_finite_set_conforming
-- name    : SennottDP.ChainASM.atas_excess_to_finite_set_conforming
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:55:17.232978+00:00
-- url     : https://prove2.me/theorems/74f9b02c-6830-42cf-9f23-ca414530feb2
-- title:
--   Proposition C.5.2 — an ATAS sending excess probability to a finite set is conforming
-- statement:
--   Let $\Gamma$ be a $z$ standard Markov chain with costs on a denumerable state space $S$, and let $G$ be a finite nonempty subset of $S$. Let $(\Gamma_N)$ be an augmentation type approximating sequence whose augmentation distributions send the excess probability to $G$:
--   $$P_{ij}(N)=P_{ij}+\sum_{r\in S-S_N}P_{ir}\,q_j(i,r,N),\qquad \sum_{j\in G}q_j(i,r,N)=1 .$$
--   Then the ATAS is conforming: for large $N$ each $\Gamma_N$ is unichain with $z$ in its positive recurrent class, and $m_{iz}(N)\to m_{iz}$, $c_{iz}(N)\to c_{iz}$ for all $i$. Moreover, if $G$ is contained in the positive recurrent class $R$ of $\Gamma$, the ATAS is also conforming on $R$: $\pi_i(N)\to\pi_i$ and $J(i)(N)\to J_R$ for $i\in R$.
--
--   Truncating a countable chain to finite state spaces and returning the truncated probability to a fixed finite set is the construction the book uses to compute average-cost optimal policies for queueing models; this result guarantees that the truncated chains' first passage moments, steady state probabilities and average costs converge.
--
--   **Formalization Note** $R$ is the communicating class of $z$, which for a $z$ standard chain is its positive recurrent class (Proposition C.2.6). The augmentation distributions are a function $q(N,i,r,j)=q_j(i,r,N)$; the excess condition sums over $G\cap S_N$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 308, Proposition C.5.2

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem atas_excess_to_finite_set_conforming {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (G : Finset S) (hG : G.Nonempty)
    (AS : ApproxSeq Γ) (q : ℕ → S → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (hexcess : AS.SendsExcessTo q (↑G : Set S)) :
    AS.IsConforming z ∧
      ((↑G : Set S) ⊆ Γ.commClass z → AS.IsConformingOn (Γ.commClass z)) := by sorry

end SennottDP.ChainASM
