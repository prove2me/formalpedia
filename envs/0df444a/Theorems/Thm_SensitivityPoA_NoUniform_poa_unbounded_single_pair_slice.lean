-- Prove2me | Theorems.Thm_SensitivityPoA_NoUniform_poa_unbounded_single_pair_slice
-- name    : SensitivityPoA.NoUniform.poa_unbounded_single_pair_slice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:16.670968+00:00
-- url     : https://prove2.me/theorems/ed469c8f-5436-485a-9164-b7c546514e71
-- title:
--   p. 25 (corrected) — the price of anarchy is unbounded on every demand slice whose demand sits on a single O/D pair
-- statement:
--   Let $(G, K, S)$ satisfy the standing assumptions and the antichain condition, let $k_0$ be an O/D pair, and let $d$ be a demand vector with $d_{k_0} > 0$ and $d_k = 0$ for every $k \neq k_0$. Then the price of anarchy is unbounded on the demand slice $\mathcal G(G,K,S)|_d = \{(\sigma, d'') \in \mathcal G(G,K,S) : d'' = d\}$: for every real $B$ there is a game $\Gamma' = (\sigma, d)$ in the game space with
--   $$\rho(\Gamma') > B.$$
--
--   Games of Pigou type — a steep polynomial cost $x^\beta$ on one path of $k_0$ against a constant cost on another — have prices of anarchy of order $\beta/\ln\beta$ (Roughgarden), which tends to $\infty$. Unboundedness on one demand slice is what contradicts a Hölder neighbourhood equal to the whole space in Theorem 8b).
--
--   **Formalization Note.** The page claims unboundedness on the demand slice of the demand vector $d$ of an *arbitrary* game. That is false for networks with several O/D pairs: with three pairs, arcs $u_i, v_i$ ($i = 1,2,3$) and $S_i = \{\{u_i\} \cup W_i, \{v_i\} \cup W_i\}$, where $W_i = \{u_j, v_j : j \neq i\}$, every pair carries a fixed load $\sum_{j\ne i} d_j$ on both $u_i$ and $v_i$, and for $d = (1,1,1)$ every game of the slice has $\rho \le 5/2$ (each two-arc subgame with background load $B = 2$ and movable demand $1$ has ratio at most $(2B+1)/B$). The statement is therefore posed for the slices whose demand sits on one pair, which is what the argument of Theorem 8b) needs (the game $\Gamma$ there may lie on any slice). For $|K| = 1$ this is the page's claim. The rate $\Theta(\beta/\ln\beta)$ is cited by the page and not posed. The antichain condition is an added hypothesis, as in the other items.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 25, proof of Theorem 8 b), third paragraph ("ρ(·) is then unbounded on the demand slice"), corrected to single-pair demand slices

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

namespace SensitivityPoA.NoUniform

theorem poa_unbounded_single_pair_slice (N : Network) (hN : N.Standing) (hA : N.Antichain)
    (d : Fin N.Sd → ℝ) (k₀ : Fin N.Sd) (hk₀ : 0 < d k₀) (hd : ∀ k, k ≠ k₀ → d k = 0)
    (B : ℝ) :
    ∃ Γ' ∈ gameSpace N, Γ'.d = d ∧ B < PoA Γ' := by sorry

end SensitivityPoA.NoUniform
