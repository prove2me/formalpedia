-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_bounds
-- name    : ScenarioReduction.Redistribution.bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:50:48.983446+00:00
-- url     : https://prove2.me/theorems/cce936b0-709c-47a0-826b-c4c5d65b1497
-- title:
--   Theorem 4 (bounds): greedy backward/forward bounds on the optimal deletion problem (13)
-- statement:
--   Under the standing assumptions of Section 3, fix $k\in\mathbb N$ with $1\le k<N$ and consider the optimal deletion problem (13),
--
--   $$\min\{D_J: J\subset\{1,\dots,N\},\ \#J=k\},$$
--
--   where $D_J$ is the optimal-weights value of Theorem 2. Choose indices recursively:
--
--   1. $l_1,\dots,l_k$ such that for $i=1,\dots,k$, $l_i$ solves $\min_{l\in\{1,\dots,N\}\setminus\{l_1,\dots,l_{i-1}\}}p_l\min_{j\neq l}c(\omega_l,\omega_j)$ — (16);
--   2. $u_1,\dots,u_{N-k}$ such that for $j=1,\dots,N-k$, $u_j$ solves
--   $$\min_{u\notin\{u_1,\dots,u_{j-1}\}}\ \sum_{i\notin\{u_1,\dots,u_{j-1},u\}}p_i\min_{l\in\{u_1,\dots,u_{j-1},u\}}c(\omega_l,\omega_i)\qquad(17),$$
--
--   and put $J_u=\{1,\dots,N\}\setminus\{u_1,\dots,u_{N-k}\}$. Then
--
--   $$\sum_{i=1}^kp_{l_i}\min_{j\neq l_i}c(\omega_{l_i},\omega_j)\le\min\{D_J:\#J=k\}\le\sum_{i\in J_u}p_i\min_{j\notin J_u}c(\omega_i,\omega_j).$$
--
--   Moreover, $\{l_1,\dots,l_k\}$ is a solution of (13) if for each $i=1,\dots,k$ the set $\arg\min_{j\neq l_i}c(\omega_{l_i},\omega_j)\setminus\{l_1,\dots,l_{i-1},l_{i+1},\dots,l_k\}$ is nonempty.
--
--   The two recursions are the backward-reduction and forward-selection heuristics of the paper; the theorem certifies the quality of their output.
--
--   **Formalization Note** Indices are 0-based: $l:\mathrm{Fin}\,k\to\mathrm{Fin}\,N$ and $u:\mathrm{Fin}(N-k)\to\mathrm{Fin}\,N$, where the natural-number subtraction $N-k$ is exact because $k<N$. The recursions are hypotheses: each $l_i$ (resp. $u_j$) is distinct from the earlier ones and minimizes (16) (resp. (17)) over the remaining indices. In (16) and in the lower bound the inner minimum ranges over all $j\neq l$, not over kept indices. The value of (13) is the infimum of $D_J$ over $\#J=k$, a finite nonempty set of reals; "solution of (13)" is stated as $\#\{l_1,\dots,l_k\}=k$ and $D_{\{l_1,\dots,l_k\}}$ equal to that value.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 503, Theorem 4, eqs. (16)–(17); problem (13) on p. 502

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset

namespace ScenarioReduction.Redistribution

theorem bounds {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k < N)
    (l : Fin k → Fin N)
    (hl : ∀ i : Fin k, l i ∉ (univ.filter (fun i' => i' < i)).image l ∧
      ∀ m ∉ (univ.filter (fun i' => i' < i)).image l,
        p (l i) * minOver {l i}ᶜ (fun j => c (ω (l i)) (ω j)) ≤ p m * minOver {m}ᶜ (fun j => c (ω m) (ω j)))
    (u : Fin (N - k) → Fin N)
    (hu : ∀ j : Fin (N - k), u j ∉ (univ.filter (fun j' => j' < j)).image u ∧
      ∀ m ∉ (univ.filter (fun j' => j' < j)).image u,
        ∑ i ∈ (insert (u j) ((univ.filter (fun j' => j' < j)).image u))ᶜ,
            p i * minOver (insert (u j) ((univ.filter (fun j' => j' < j)).image u)) (fun l' => c (ω l') (ω i))
          ≤ ∑ i ∈ (insert m ((univ.filter (fun j' => j' < j)).image u))ᶜ,
            p i * minOver (insert m ((univ.filter (fun j' => j' < j)).image u)) (fun l' => c (ω l') (ω i))) :
    ∑ i : Fin k, p (l i) * minOver {l i}ᶜ (fun j => c (ω (l i)) (ω j)) ≤ optimalDeletionValue c ω p k ∧
      optimalDeletionValue c ω p k ≤
        ∑ i ∈ (univ.image u)ᶜ, p i * minOver (univ.image u) (fun j => c (ω i) (ω j)) ∧
      ((∀ i : Fin k, ∃ j : Fin N, j ≠ l i ∧ (∀ i' : Fin k, i' ≠ i → j ≠ l i') ∧
          ∀ j' : Fin N, j' ≠ l i → c (ω (l i)) (ω j) ≤ c (ω (l i)) (ω j')) →
        (univ.image l).card = k ∧ optWeightsValue c ω p (univ.image l) = optimalDeletionValue c ω p k) := by sorry

end ScenarioReduction.Redistribution
