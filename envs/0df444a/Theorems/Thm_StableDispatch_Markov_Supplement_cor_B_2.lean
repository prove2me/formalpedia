-- Prove2me | Theorems.Thm_StableDispatch_Markov_Supplement_cor_B_2
-- name    : StableDispatch.Markov.Supplement.cor_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T09:44:54.524741+00:00
-- url     : https://prove2.me/theorems/7a3ec3fe-be25-4e99-ab46-b10d6ba67a26
-- title:
--   Corollary B.2, p. 19 — with o(log n) memory, sampled sets of the same small size are equally likely
-- statement:
--   Fix a sequence of weakly symmetric memory-based dispatching policies ($n\ge1$) with $|\mathcal M_n|\le 2^{c_n}$ and $c_n\in o(\log n)$, and let $U$ be uniform on $[0,1]$. Let $(s_n)$ be any sequence with $s_n\in o(n)$. Then for all $n$ large enough, for every memory state $m\in\mathcal M_n$, every job size $w\ge0$, every set of servers $S$ with $|S|\le s_n$ and every permutation $\sigma$ of the servers,
--
--   $$\mathbb P\big(f_1(m,w,U)=S\big)=\mathbb P\big(f_1(m,w,U)=\sigma(S)\big).$$
--
--   All sets of servers of the same (small) size are equally likely to be sampled at an arrival, although the memory state and the job size may influence how many servers are sampled. In the proof of Theorem 2.2 this gives a lower bound on the probability that every sampled server is slow.
--
--   **Formalization Note** $\sigma(S)$ is the image `S.map σ`. "$|S|\in o(n)$" is expressed by an arbitrary sequence $s_n=o(n)$ bounding $|S|$.
--
--   Differences from the source:
--
--   - reading: the standing hypothesis of Appendix B (p. 18): a fixed sequence of weakly symmetric policies (Assumption 2.1) with c_n ∈ o(log n) bits of memory → explicit hypotheses: a sequence of policies (P n) for n ≥ 1, each weakly symmetric, with |M_n| ≤ 2^{c_n} and c_n =o(log n) (Asymptotics.IsLittleO); reason: the proposition is stated under this standing hypothesis; the message-rate bound α_n is not used by it and is not assumed
--   - generalization: M_n = {1, …, 2^{c_n}} (exactly 2^{c_n} memory states) → the memory is Fin memSize with 1 ≤ memSize ≤ 2^{c_n}, c_n real; reason: Theorem 2.2 speaks of 'at most c_n bits'; memSize = 2^{c_n} is the paper's case
--   - reading: '|S| ∈ o(n)' for one set S, and 'for all n large enough' → for every sequence s_n = o(n) there is N such that for every n ≥ N the claim holds for every memory state, every admissible argument and every S with |S| ≤ s_n; N may depend on (s_n), (c_n) and the policy sequence; reason: o(n) is a property of a sequence; this is the only reading under which the proof of Theorem 2.2 (p. 21, s*_n = α_n/(λnp_{1/2}) ∈ o(n)) can use it
--   - encoding: servers {1, …, n}; maps on M_n × ℝ₊ × [0, 1]; U uniform on [0, 1] → servers Fin n (0-based); the maps take real arguments and are quantified only at w ≥ 0; U has law unif = Lebesgue measure on [0, 1]; policies exist only for n ≥ 1, so the sequence is indexed by n ≥ 1; reason: Lean conventions; the values off ℝ₊ and off [0, 1] never enter
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 19, Corollary B.2

import Mathlib
import Definitions.Def_StableDispatch_Markov_Supplement_Policy

namespace StableDispatch.Markov.Supplement

open MeasureTheory Asymptotics Filter

theorem cor_B_2 (c : ℕ → ℝ) (hc : c =o[atTop] (fun n : ℕ => Real.log n))
    (P : ∀ n : ℕ, 1 ≤ n → Policy n) (hsym : ∀ n (hn : 1 ≤ n), WeaklySymmetric (P n hn))
    (hmem : ∀ n (hn : 1 ≤ n), ((P n hn).memSize : ℝ) ≤ (2 : ℝ) ^ c n)
    (s : ℕ → ℝ) (hs : s =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ N : ℕ, ∀ n (hn : 1 ≤ n), N ≤ n →
      ∀ (m : Fin (P n hn).memSize) (w : ℝ), 0 ≤ w →
      ∀ S : Finset (Fin n), (S.card : ℝ) ≤ s n →
      ∀ σ : Equiv.Perm (Fin n),
        unif {u | (P n hn).f1 m w u = S} =
          unif {u | (P n hn).f1 m w u = S.map σ.toEmbedding} := by sorry

end StableDispatch.Markov.Supplement
