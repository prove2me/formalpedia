-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_11
-- name    : SubmodMDP.Policies.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:51.164948+00:00
-- url     : https://prove2.me/theorems/f4e011d5-2cbb-4cc5-a511-86bc54796077
-- title:
--   Lemma 11 — Algorithm 4 simulates $p$ at chance vertices
-- statement:
--   Let $G$ be a layered MDP graph with $H=d^r$ ($d\ge2$, $r\ge1$), and let $x\in Q^{(r)}$ satisfy (7). If Algorithm 4 is called with $x$ and a trajectory $v_1,\dots,v_\ell$ ($v_i\in V_i$) ending in a chance vertex $v_\ell\in C$, then either "error" is returned, or the returned distribution of $v_{\ell+1}$ is exactly $p_{v_\ell}$:
--   $$\frac{x_{I\cup\{u\}}}{x_I}=p_{v_\ell}(u)\qquad\text{for all }u\in V_{\ell+1},$$
--   and the returned weight of every vertex outside $V_{\ell+1}$ is $0=p_{v_\ell}(u)$.
--
--   Thus the policy of Algorithm 4, if run also at chance vertices, reproduces the environment there.
--
--   Differences from the source:
--   - encoding: "error" is returned or v_{ℓ+1} is chosen according to p_{v_ℓ} → alg4 = none, or alg4 returns a weight vector equal to p_{v_ℓ} at every vertex; reason: error is the value none; a law is determined by its weights
--   - encoding: a trajectory v₁, …, v_ℓ ∈ V₁ × ⋯ × V_ℓ (Algorithm 4's input) ending in a chance vertex → explicit hypotheses 1 ≤ ℓ ≤ H − 1 and v_i ∈ V_i; reason: ℓ ≥ 1 because the trajectory ends in a vertex, ℓ ≤ H − 1 because V_{ℓ+1} must exist; these only exclude undefined calls
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 11, p. 19 (PDF p. 20); Algorithm 4, p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_GraphMDP

namespace SubmodMDP.Policies

/-- Lemma 11 (PDF p. 19): for `x ∈ Q^(r)` satisfying (7) and a trajectory `v₁, …, v_ℓ`
(`v_i ∈ V_i`) ending in a chance vertex, Algorithm 4 either returns "error" or returns exactly
the transition distribution `p_{v_ℓ}`. -/
theorem lemma_11 (M : GMDP) (hM : M.WF) (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hH : M.G.H = d ^ r) (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) (h7 : Sat7 M r x)
    (traj : List (Fin M.G.N)) (hlen1 : 1 ≤ traj.length) (hlen2 : traj.length ≤ M.G.H - 1)
    (hlayer : ∀ (i : ℕ) (h : i < traj.length), M.G.layer traj[i] = i + 1)
    (vℓ : Fin M.G.N) (hlast : traj.getLast? = some vℓ) (hc : M.chance vℓ = true) :
    alg4 M d x traj = none ∨ ∃ q, alg4 M d x traj = some q ∧ ∀ u, q u = M.p vℓ u := by sorry

end SubmodMDP.Policies
