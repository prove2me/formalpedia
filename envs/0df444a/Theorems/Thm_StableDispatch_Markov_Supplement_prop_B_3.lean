-- Prove2me | Theorems.Thm_StableDispatch_Markov_Supplement_prop_B_3
-- name    : StableDispatch.Markov.Supplement.prop_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:46:17.437813+00:00
-- url     : https://prove2.me/theorems/870fafb8-16a9-4ea9-81e5-d3b781dc9cfd
-- title:
--   Proposition B.3, p. 20 — with o(log n) memory, the destination is uniform outside the queried set
-- statement:
--   Fix a sequence of weakly symmetric memory-based dispatching policies ($n\ge1$) with $|\mathcal M_n|\le 2^{c_n}$ and $c_n\in o(\log n)$. Let $f_2$ be the dispatching map of the $n$-th policy, which receives the memory state $m$, the job size $w$ and the set $\{(q_i,\mu_i,i):i\in S\}$ of states and rates of the queried servers, and let $V$ be uniform on $[0,1]$. Let $(s_n)$ be any sequence with $s_n\in o(n)$. Then for all $n$ large enough, for every $m\in\mathcal M_n$, every set $S$ with $|S|\le s_n$, every queue state vector $q\in\mathcal Q^n$ (nonnegative workload sequences), every rate vector $\mu\in\mathbb R^n_+$ and every $w\ge0$,
--
--   $$\mathbb P\Big(f_2\big(m,w,\{(q_i,\mu_i,i):i\in S\},V\big)=j\Big)\ \text{is the same for all } j\notin S.$$
--
--   Outside the set of queried servers, the destination of a job is uniformly distributed (possibly with total probability zero). In the proof of Theorem 2.2 this yields a positive fraction of jobs routed to slow servers.
--
--   **Formalization Note** The set of triples is encoded as the partial map $i\mapsto(q_i,\mu_i)$ on $S$ (`info S q μ`). "$|S|\in o(n)$" is expressed by an arbitrary sequence $s_n=o(n)$ bounding $|S|$.
--
--   Differences from the source:
--
--   - reading: the standing hypothesis of Appendix B (p. 18): a fixed sequence of weakly symmetric policies (Assumption 2.1) with c_n ∈ o(log n) bits of memory → explicit hypotheses: a sequence of policies (P n) for n ≥ 1, each weakly symmetric, with |M_n| ≤ 2^{c_n} and c_n =o(log n) (Asymptotics.IsLittleO); reason: the proposition is stated under this standing hypothesis; the message-rate bound α_n is not used by it and is not assumed
--   - generalization: M_n = {1, …, 2^{c_n}} (exactly 2^{c_n} memory states) → the memory is Fin memSize with 1 ≤ memSize ≤ 2^{c_n}, c_n real; reason: Theorem 2.2 speaks of 'at most c_n bits'; memSize = 2^{c_n} is the paper's case
--   - reading: '|S| ∈ o(n)' for one set S, and 'for all n large enough' → for every sequence s_n = o(n) there is N such that for every n ≥ N the claim holds for every memory state, every admissible argument and every S with |S| ≤ s_n; N may depend on (s_n), (c_n) and the policy sequence; reason: o(n) is a property of a sequence; this is the only reading under which the proof of Theorem 2.2 (p. 21, s*_n = α_n/(λnp_{1/2}) ∈ o(n)) can use it
--   - encoding: servers {1, …, n}; maps on M_n × ℝ₊ × [0, 1]; U uniform on [0, 1] → servers Fin n (0-based); the maps take real arguments and are quantified only at w ≥ 0; U has law unif = Lebesgue measure on [0, 1]; policies exist only for n ≥ 1, so the sequence is indexed by n ≥ 1; reason: Lean conventions; the values off ℝ₊ and off [0, 1] never enter
--   - encoding: {(q_i, µ_i, i) : i ∈ S} ∈ B_n, q ∈ Q^n = (ℝ₊^{ℤ₊})^n, µ ∈ ℝ^n_+ → info S q μ (the partial map i ↦ (q_i, μ_i) on S), with q : Fin n → ℕ → ℝ and μ : Fin n → ℝ assumed nonnegative; reason: a set of triples with distinct third coordinates is the same as a partial map from server indices
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 20, Proposition B.3

import Mathlib
import Definitions.Def_StableDispatch_Markov_Supplement_Policy

namespace StableDispatch.Markov.Supplement

open MeasureTheory Asymptotics Filter

theorem prop_B_3 (c : ℕ → ℝ) (hc : c =o[atTop] (fun n : ℕ => Real.log n))
    (P : ∀ n : ℕ, 1 ≤ n → Policy n) (hsym : ∀ n (hn : 1 ≤ n), WeaklySymmetric (P n hn))
    (hmem : ∀ n (hn : 1 ≤ n), ((P n hn).memSize : ℝ) ≤ (2 : ℝ) ^ c n)
    (s : ℕ → ℝ) (hs : s =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ N : ℕ, ∀ n (hn : 1 ≤ n), N ≤ n →
      ∀ (m : Fin (P n hn).memSize) (S : Finset (Fin n)), (S.card : ℝ) ≤ s n →
      ∀ (q : Fin n → Queue), (∀ i k, 0 ≤ q i k) →
      ∀ (μ : Fin n → ℝ), (∀ i, 0 ≤ μ i) →
      ∀ (w : ℝ), 0 ≤ w →
      ∀ j ∉ S, ∀ j' ∉ S,
        unif {v | (P n hn).f2 m w (info S q μ) v = j} =
          unif {v | (P n hn).f2 m w (info S q μ) v = j'} := by sorry

end StableDispatch.Markov.Supplement
