-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_10
-- name    : SubmodMDP.Policies.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:57.060186+00:00
-- url     : https://prove2.me/theorems/7877f21e-a201-45e5-9e5f-32d59cc7937c
-- title:
--   Lemma 10 — visit probabilities of an MDP policy satisfy (7)
-- statement:
--   Let $G$ be a layered MDP graph (chance vertices $C$, decision vertices $D$, start $s$, transition probabilities $p$), let $\pi$ be a randomized policy, and let $\mathrm{OPT}\sim\mathcal O$ be the path produced by the MDP process that applies $\pi$ on decision vertices and $p$ on chance vertices. Then the vector
--   $$x_I=\mathbb E\big[(\mathbf 1^{(r)}_{\mathrm{OPT}})_I\big]=\mathbb P[I\subseteq\mathrm{OPT}]$$
--   satisfies (7):
--   $$x_{I\cup\{u\}}=x_I\cdot p_c(u)\qquad i\in\{1,\dots,H-1\},\ c\in V_i\cap C,\ u\in V_{i+1},\ \{c\}\subseteq I\subseteq V_1\cup\dots\cup V_i,\ |I|\le r.$$
--
--   In the proof of Theorem 2 this is applied to an optimal policy: its visit probabilities form a feasible distribution for the constraints (7), so Lemma 7 compares against it.
--
--   Differences from the source:
--   - generalization: O arises from the MDP process with the optimal policy; standing assumption H = d^r of §3 → any valid randomized policy π; no assumption on H; reason: the proof never uses optimality or H = d^r; the statement specializes to an optimal policy with H = d^r
--   - encoding: transition probabilities p_c(v), policies π_{v≤ℓ} → real-valued p and π, π required to be a distribution on out-neighbours on every walk from s of length < H ending in a decision vertex; reason: the paper's model; walks of length ≥ H have no successor
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 10, p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_GraphMDP

namespace SubmodMDP.Policies

/-- Lemma 10 (PDF p. 18), stated for every valid policy: the visit moments
`x_I = P[I ⊆ OPT]` of the path `OPT` produced by the MDP process (policy `π` on decision
vertices, `p` on chance vertices) satisfy constraint (7). -/
theorem lemma_10 (M : GMDP) (hM : M.WF) (π : GPolicy M) (hπ : IsGPolicy M π) (r : ℕ) :
    Sat7 M r (visitMoment M π) := by sorry

end SubmodMDP.Policies
