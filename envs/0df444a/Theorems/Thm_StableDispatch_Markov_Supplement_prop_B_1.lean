-- Prove2me | Theorems.Thm_StableDispatch_Markov_Supplement_prop_B_1
-- name    : StableDispatch.Markov.Supplement.prop_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:44:22.627199+00:00
-- url     : https://prove2.me/theorems/fbc6c221-2269-4636-a751-6a460d0e90c7
-- title:
--   Proposition B.1, p. 18 — with o(log n) memory, the server sampled beyond S is uniform outside S
-- statement:
--   Fix a sequence of memory-based dispatching policies, one for each number of servers $n\ge1$, that are weakly symmetric (Assumption 2.1) and have at most $c_n$ bits of memory, $|\mathcal M_n|\le 2^{c_n}$, where $c_n\in o(\log n)$. Let $f_1:\mathcal M_n\times\mathbb R_+\times[0,1]\to\mathcal P(\{1,\dots,n\})$ be the sampling map of the $n$-th policy and $U$ uniform on $[0,1]$. For a memory state $m$, a job size $w\ge0$ and a set of servers $S$, let
--
--   $$B(m,w;S)=\{\,f_1(m,w,U)=S\cup\{i\}\ \text{for some } i\notin S\,\}.$$
--
--   Let $(s_n)$ be any sequence with $s_n\in o(n)$. Then for all $n$ large enough, for every $m\in\mathcal M_n$, every $w\ge0$ and every $S$ with $|S|\le s_n$ such that $\mathbb P(B(m,w;S))>0$,
--
--   $$\mathbb P\big(j\in f_1(m,w,U)\,\big|\,B(m,w;S)\big)\ \text{is the same for all } j\notin S.$$
--
--   Given that the dispatcher samples $S$ and exactly one more server, that extra server is uniformly distributed over the complement of $S$: with little memory, a weakly symmetric policy cannot favour any particular server. This is the combinatorial input to Corollary B.2 and to the proof of Theorem 2.2.
--
--   **Formalization Note** The conditional probability is `ProbabilityTheory.cond` of the uniform law on $[0,1]$. The paper's "$|S|\in o(n)$" is expressed through an arbitrary sequence $s_n=o(n)$ bounding $|S|$, with a threshold uniform in $m$, $w$ and $S$.
--
--   Differences from the source:
--
--   - reading: the standing hypothesis of Appendix B (p. 18): a fixed sequence of weakly symmetric policies (Assumption 2.1) with c_n ∈ o(log n) bits of memory → explicit hypotheses: a sequence of policies (P n) for n ≥ 1, each weakly symmetric, with |M_n| ≤ 2^{c_n} and c_n =o(log n) (Asymptotics.IsLittleO); reason: the proposition is stated under this standing hypothesis; the message-rate bound α_n is not used by it and is not assumed
--   - generalization: M_n = {1, …, 2^{c_n}} (exactly 2^{c_n} memory states) → the memory is Fin memSize with 1 ≤ memSize ≤ 2^{c_n}, c_n real; reason: Theorem 2.2 speaks of 'at most c_n bits'; memSize = 2^{c_n} is the paper's case
--   - reading: '|S| ∈ o(n)' for one set S, and 'for all n large enough' → for every sequence s_n = o(n) there is N such that for every n ≥ N the claim holds for every memory state, every admissible argument and every S with |S| ≤ s_n; N may depend on (s_n), (c_n) and the policy sequence; reason: o(n) is a property of a sequence; this is the only reading under which the proof of Theorem 2.2 (p. 21, s*_n = α_n/(λnp_{1/2}) ∈ o(n)) can use it
--   - encoding: servers {1, …, n}; maps on M_n × ℝ₊ × [0, 1]; U uniform on [0, 1] → servers Fin n (0-based); the maps take real arguments and are quantified only at w ≥ 0; U has law unif = Lebesgue measure on [0, 1]; policies exist only for n ≥ 1, so the sequence is indexed by n ≥ 1; reason: Lean conventions; the values off ℝ₊ and off [0, 1] never enter
--   - encoding: 'assume that the conditional probability measure P(· | B(m, w; S)) is well-defined' → 0 < unif B(m, w; S); reason: a conditional probability given an event is defined exactly when the event has positive probability
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 18, Proposition B.1 (standing hypothesis p. 18)

import Mathlib
import Definitions.Def_StableDispatch_Markov_Supplement_Policy

namespace StableDispatch.Markov.Supplement

open MeasureTheory ProbabilityTheory Asymptotics Filter

theorem prop_B_1 (c : ℕ → ℝ) (hc : c =o[atTop] (fun n : ℕ => Real.log n))
    (P : ∀ n : ℕ, 1 ≤ n → Policy n) (hsym : ∀ n (hn : 1 ≤ n), WeaklySymmetric (P n hn))
    (hmem : ∀ n (hn : 1 ≤ n), ((P n hn).memSize : ℝ) ≤ (2 : ℝ) ^ c n)
    (s : ℕ → ℝ) (hs : s =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ N : ℕ, ∀ n (hn : 1 ≤ n), N ≤ n →
      ∀ (m : Fin (P n hn).memSize) (w : ℝ), 0 ≤ w →
      ∀ S : Finset (Fin n), (S.card : ℝ) ≤ s n →
        0 < unif {u | ∃ i ∉ S, (P n hn).f1 m w u = insert i S} →
        ∀ j ∉ S, ∀ j' ∉ S,
          unif[|{u | ∃ i ∉ S, (P n hn).f1 m w u = insert i S}] {u | j ∈ (P n hn).f1 m w u} =
            unif[|{u | ∃ i ∉ S, (P n hn).f1 m w u = insert i S}]
              {u | j' ∈ (P n hn).f1 m w u} := by sorry

end StableDispatch.Markov.Supplement
