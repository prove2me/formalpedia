-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_blocked_mem_span
-- name    : SeqPostedPricing.MatroidSPM.blocked_mem_span
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:43:54.257237+00:00
-- url     : https://prove2.me/theorems/597a5946-4a1b-42aa-a9e7-b57d64898fa3
-- title:
--   Proof of Thm 5: the sets $B_j$ partition the blocked agents and a blocked agent of $B_j$ comes after $i_j$ (corrected: blocked agents outside $\mathrm{span}(\emptyset)$)
-- statement:
--   Let $\mathcal J$ be a matroid and run the SPM with any set of agents it makes offers to, prices non-increasing along the order $\sigma$ on those agents, and any value profile $\mathbf v$. Let $S=\{i_1,\dots,i_\ell\}$ be the served agents in order, $S_j$ the first $j$ of them, and
--
--   $$
--   B_j=\mathrm{span}(S_j)\setminus\mathrm{span}(S_{j-1})\qquad(1\le j\le\ell).
--   $$
--
--   Let the agent $\sigma(t)$ of step $t$ be blocked (one the SPM makes offers to, but whose addition to the agents served before it is infeasible) and not in $\mathrm{span}(\emptyset)$. Then $\sigma(t)$ lies in exactly one $B_j$, the agent $i_j$ is served at a step before $t$, and $p_{\sigma(t)}\le p_{i_j}$.
--
--   In the Lean statement $A_s$ is the set of agents served in the steps before $s$; the $j$ above corresponds to the unique step $s$ with $\sigma(t)\in\mathrm{span}(A_{s+1})\setminus\mathrm{span}(A_s)$, at which $i_j=\sigma(s)$ is served, $A_s=S_{j-1}$ and $A_{s+1}=S_j$.
--
--   Differences from the source:
--   - correction: the sets B_j partition the set of blocked agents → every blocked agent not in span(∅) lies in exactly one B_j; reason: a blocked agent i with {i} ∉ J lies in span(∅) = span(S_0) and in no B_j with j ≥ 1: one agent, J = {∅}, the agent is never offered (blocked), ℓ = 0 and there is no B_j; such agents have q_i ≤ rank({i}) = 0 in the proof
--   - correction: B_j ⊆ {i : i ≥ i_j} and p_i ≤ p_{i_j} for all i ∈ B_j → for a blocked agent σ(t) of B_j, the step s at which i_j is served satisfies s < t, and p_{σ(t)} ≤ p_{σ(s)}; reason: over all of B_j the inclusion is false: one item (1-uniform matroid), agent a priced 1 offered first and rejecting, agent b priced ½ accepting; S = {b}, B_1 = span({b}) \ span(∅) = {a, b}, and a comes before i_1 = b; the proof applies it to the blocked agents of B_j only
--   - generalization: the mechanism S (Myerson's prices, decreasing order) → any set of agents offered to, any prices non-increasing along σ on it, any value profile; reason: the fact is combinatorial and uses only the decreasing order; S is an instance
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, proof of Theorem 5, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_span
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmOffered
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsDecreasingOrder

namespace SeqPostedPricing.MatroidSPM

/-- **The sets `B_j = span(S_j) \ span(S_{j−1})` partition the blocked agents, and a blocked agent
of `B_j` comes after `i_j`, at a price at most `p_{i_j}` (corrected: blocked agents outside
`span(∅)`).**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, proof of Theorem 5, unnumbered, p. 6 (PDF p. 8): "Define the sets Bj = span(Sj) \
span(Sj−1). Note that the sets Bj partition the set of blocked agents. Moreover, Bj ⊆ {i : i ≥
ij}, since we condition on serving S, and so, pi ≤ p_{ij} for all i ∈ Bj."

For a matroid `J`, any prices non-increasing along the order `σ` on the active agents, and any
value profile: let the active agent `σ t` of step `t` be blocked (not offered service) and not in
`span(∅)`. Then there is exactly one step `s` with `σ t ∈ span(A_{s+1}) \ span(A_s)` (`A_s` the
set of agents served in the steps before `s`); at that step `s < t`, the agent `σ s` is served
(so `A_s = S_{j−1}`, `A_{s+1} = S_j`, `σ s = i_j` and `σ t ∈ B_j`), and `p_{σ t} ≤ p_{σ s}`.

**Formalization Note.** `S_j` is the set of the first `j` served agents, which is the set `A_s`
served before the step `s` at which `i_{j+1}` is served; existence and uniqueness of `s` is the
partition claim. A blocked agent in `span(∅)` (an agent `i` with `{i} ∉ J`) lies in no `B_j`
with `j ≥ 1`, so the printed partition claim is corrected by excluding it (such agents have
`q_i ≤ rank({i}) = 0` in the proof). -/
theorem blocked_mem_span {n : ℕ} (Feas : Finset (Fin n) → Prop) (hmat : IsMatroid Feas)
    (p : Fin n → ℝ) (active : Finset (Fin n)) (σ : Fin n ≃ Fin n)
    (hσ : IsDecreasingOrder p active σ) (v : Fin n → ℝ) (t : Fin n)
    (ht : σ t ∈ active) (hblk : ¬ spmOffered Feas p active σ v t)
    (hloop : σ t ∉ span Feas ∅) :
    ∃ s : Fin n, s < t ∧
      σ s ∈ spmServedBefore Feas p active σ v ((s : ℕ) + 1) ∧
      σ s ∉ spmServedBefore Feas p active σ v (s : ℕ) ∧
      σ t ∈ span Feas (spmServedBefore Feas p active σ v ((s : ℕ) + 1)) ∧
      σ t ∉ span Feas (spmServedBefore Feas p active σ v (s : ℕ)) ∧
      p (σ t) ≤ p (σ s) ∧
      ∀ s' : Fin n,
        σ t ∈ span Feas (spmServedBefore Feas p active σ v ((s' : ℕ) + 1)) →
        σ t ∉ span Feas (spmServedBefore Feas p active σ v (s' : ℕ)) → s' = s := by sorry

end SeqPostedPricing.MatroidSPM
