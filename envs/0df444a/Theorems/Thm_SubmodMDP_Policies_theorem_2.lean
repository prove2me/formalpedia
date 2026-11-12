-- Prove2me | Theorems.Thm_SubmodMDP_Policies_theorem_2
-- name    : SubmodMDP.Policies.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:35.248013+00:00
-- url     : https://prove2.me/theorems/16e8ad4e-706e-4e3d-a9f5-87023e7e2c1f
-- title:
--   Theorem 2 (corrected: memory $\lceil c/\varepsilon\rceil$ for large $\varepsilon$) — randomized $O(\log H)$- and $O(H^\varepsilon)$-approximate policies with short memory
-- statement:
--   Consider a submodular MDP with state set $S$, action set $A$, horizon $H$, rational initial and transition probabilities, and a non-negative monotone submodular reward $f:2^{S\sqcup A}\to\mathbb Q_{\ge0}$ given by a value oracle. Let $n=|S|+|A|+H$, let $\langle p\rangle$ be the encoding size of the initial and transition probabilities, and let $\mathrm{OPT}$ be the supremum of $V(\pi)=\mathbb E[f(\{s_1,a_1,\dots,s_H,a_H\})]$ over all randomized history-dependent policies.
--
--   1. **Logarithmic regime.** There is a randomized algorithm running in time $n^{O(\log H)}\langle p\rangle^{O(1)}$ that computes a policy $\pi_\sigma$, each of whose decisions is evaluated in the same time, such that with probability at least $1-1/n$
--   $$V(\pi_\sigma)\ \ge\ \frac{\mathrm{OPT}}{O(\log H)},$$
--   and at time $t$ the policy depends only on $O(\log H)$ entries of the trajectory $s_1,a_1,\dots,s_t$, at positions fixed in advance.
--   2. **Polynomial regime.** For every $\varepsilon>0$ there is such an algorithm running in time $n^{O(1/\varepsilon)}\langle p\rangle^{O(1)}$ with
--   $$V(\pi_\sigma)\ \ge\ \frac{\mathrm{OPT}}{O_\varepsilon(H^\varepsilon)},$$
--   whose decisions depend on $O(1/\varepsilon)$ entries of the trajectory (at least one).
--
--   Concretely: there are absolute constants $C>0$ and $c$ with time $(n+1)^{c(\lfloor\log_2H\rfloor+1)}(\langle p\rangle+1)^c$, ratio $C(\lfloor\log_2H\rfloor+1)$ and memory $c(\lfloor\log_2H\rfloor+1)$ in the first regime; and an absolute $c$ such that for every $\varepsilon>0$ there is $C_\varepsilon>0$ with time $(n+1)^{\lceil c/\varepsilon\rceil}(\langle p\rangle+1)^c$, ratio $C_\varepsilon H^\varepsilon$ and memory $\lceil c/\varepsilon\rceil$ in the second.
--
--   Before this result the best approximation ratio for submodular MDPs without further assumptions was $O(H)$.
--
--   Differences from the source:
--   - encoding: finite sets S, A; n = poly(|S|, |A|, H) → S = {0, …, n_S − 1}, A = {0, …, n_A − 1} with n_S, n_A ≥ 1, and n = |S| + |A| + H; reason: an instance is given with an enumeration of S and A; every poly(|S|,|A|,H) changes only the constant c
--   - encoding: log H in O(log H) and n^{O(log H)} → ⌊log₂ H⌋ + 1; reason: avoids log 1 = 0 at H = 1; same asymptotic class
--   - encoding: time n^{O(log H)}⟨p⟩^{O(1)}, resp. n^{O(1/ε)}⟨p⟩^{O(1)} → (n+1)^{c(⌊log₂H⌋+1)}(⟨p⟩+1)^c, resp. (n+1)^{⌈c/ε⌉}(⟨p⟩+1)^c, with one absolute c, for the preprocessing program and for every decision; reason: instantiation of O(·) with explicit constants; (n+1), (⟨p⟩+1) avoid degenerate bases
--   - encoding: ⟨p⟩, the encoding size of the transition probabilities → total bit length of numerators and denominators (in lowest terms) of all initial and transition probabilities; reason: the standard encoding size; the initial probabilities are part of the transition data of the input
--   - reading: O(log H)-approximate, resp. O(H^ε)-approximate → ratio C(⌊log₂H⌋+1) with absolute C > 0, resp. C_ε H^ε with C_ε > 0 depending on ε; reason: the source obtains the second regime by rescaling ε (p. 13, PDF p. 14), which only gives an ε-dependent constant; the time and memory exponents stay absolute
--   - reading: a randomized … approximate policy that can be computed in … time → a randomized preprocessing program outputs a description σ; a deterministic decision program computes the action distribution of π_σ from σ and the trajectory within the same bound; with probability ≥ 1 − 1/n over the coins, V(π_σ) ≥ OPT / ratio; reason: the proof gives success probability 1 − n'^{−1/ε'} through Lemma 7 for the reduced graph with n' ≥ n vertices; the high-probability reading implies the in-expectation one
--   - reading: the agent only needs to remember O(log H) many states and actions from the trajectory → a set K(H,t) of positions of the trajectory s₁, a₁, …, s_t, chosen before σ and the coins, with |K(H,t)| ≤ c(⌊log₂H⌋+1), such that the decision depends only on t and on the entries at K(H,t); reason: Algorithm 4 conditions on the vertices at the positions K, which depend only on ℓ and H
--   - correction: in the latter O(1/ε) many (for every ε > 0) → at most ⌈c/ε⌉ entries; reason: any bound c/ε is < 1 for ε > c and forces the decision to ignore the trajectory; counterexample: H = 2, m states, s₁ uniform, action a from state s leads to a goal state g if a = s and to a dead state otherwise, f(X) = [g ∈ X]; OPT = 1, every trajectory-independent policy has value 1/m < 1/(C_ε 2^ε) for m large; ⌈c/ε⌉ ≥ 1 allows the current state, which the source's algorithm with r = 1 uses
--   - reading: f : 2^V → ℝ≥0 monotone submodular, given by a value oracle → f : Finset V → ℚ with 0 ≤ f, monotone and submodular after the cast to ℝ, accessed only through the machine's query instruction; reason: footnote 2 requires every value of f to fit in a word, which forces a finite representation
--   - reading: running time as the number of word-RAM operations, words large enough to store every input value and every value of f (footnote 2); no fixed instruction set or randomness primitive → the randomized value-oracle integer RAM of SubmodMDP.Policies.Machine: integer registers, +, -, ×, floor division/modulus, indirect addressing, jumps, a value-oracle query and rand M (uniform on {0,…,M-1}); an instruction on operands of k words of w bits costs (1+k)², a query on m indices (1+m)(1+k)², w covers ⌈log₂(input length+2)⌉, every input integer and every numerator/denominator of f; every run must halt within the bound; reason: footnote 2 fixes only the word size; every instruction is simulable on a w-bit word RAM in O(cost) operations, so a bound here implies the paper's; exact sampling (rand M) is needed because with fair coins only, an exact law with probabilities 1/3 cannot be produced within a worst-case bound, which would falsify the exact distributional claims
--   - generalization: transition probabilities P[s_{t+1} = s' | s_t = s, a_t = a] determined by s_t and a_t → transition probabilities that may also depend on t ∈ {1, …, H − 1}; reason: Eq. (1) is indexed by t; the time-homogeneous model is the constant family, and the reduction of §3 builds one chance layer per time step
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Theorem 2, p. 3 (PDF p. 4); model §1.1, p. 2 (PDF p. 3); footnotes 1–2, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_MDP
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SubmodMDP.Policies

open NonmonotoneSubmod.Shared SubsamplingSM.Offline

/-- Theorem 2 (PDF p. 4), both regimes. `n = |S| + |A| + H`, `⟨p⟩ = Inst.encSize`, `log H` is
`⌊log₂ H⌋ + 1`.

1. There are absolute constants `C > 0`, `c`, a randomized program `Pre`, a deterministic program
   `Dec` and memory positions `K H t` with `|K H t| ≤ c(⌊log₂ H⌋+1)` such that on every valid
   instance and every non-negative monotone submodular rational reward `f` (value oracle), `Pre`
   and `Dec` run within cost `(n+1)^{c(⌊log₂ H⌋+1)} (⟨p⟩+1)^c`, the decisions of `π_σ` depend only
   on the trajectory entries at `K H t`, and with probability at least `1 - 1/n`,
   `V(π_σ) ≥ OPT / (C (⌊log₂ H⌋+1))`.
2. There is an absolute constant `c` such that for every `ε > 0` there are `C_ε > 0`, `Pre`,
   `Dec`, `K` with `|K H t| ≤ ⌈c/ε⌉`, cost `(n+1)^{⌈c/ε⌉} (⟨p⟩+1)^c`, and with probability at
   least `1 - 1/n`, `V(π_σ) ≥ OPT / (C_ε H^ε)`. -/
theorem theorem_2 :
    (∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∃ Pre Dec : Program, Dec.Deterministic ∧
      ∃ K : ℕ → ℕ → Finset ℕ,
        (∀ H t : ℕ, (K H t).card ≤ c * (Nat.log 2 H + 1) ∧ ∀ i ∈ K H t, i < 2 * t - 1) ∧
        ∀ I : Inst, I.Valid →
        ∀ f : Finset (Elem I) → ℚ, (∀ X, 0 ≤ f X) → IsMonotoneSetFn (fun X => (f X : ℝ)) →
          Submodular (fun X => (f X : ℝ)) →
        IsPolicyAlgorithm Pre Dec K I f
          ((I.n + 1) ^ (c * (Nat.log 2 I.H + 1)) * (I.encSize + 1) ^ c)
          (C * ((Nat.log 2 I.H : ℝ) + 1)) (1 - 1 / (I.n : ℝ))) ∧
    (∃ c : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ Pre Dec : Program, Dec.Deterministic ∧
      ∃ K : ℕ → ℕ → Finset ℕ,
        (∀ H t : ℕ, (K H t).card ≤ ⌈(c : ℝ) / ε⌉₊ ∧ ∀ i ∈ K H t, i < 2 * t - 1) ∧
        ∀ I : Inst, I.Valid →
        ∀ f : Finset (Elem I) → ℚ, (∀ X, 0 ≤ f X) → IsMonotoneSetFn (fun X => (f X : ℝ)) →
          Submodular (fun X => (f X : ℝ)) →
        IsPolicyAlgorithm Pre Dec K I f
          ((I.n + 1) ^ ⌈(c : ℝ) / ε⌉₊ * (I.encSize + 1) ^ c)
          (C * (I.H : ℝ) ^ ε) (1 - 1 / (I.n : ℝ))) := by sorry

end SubmodMDP.Policies
