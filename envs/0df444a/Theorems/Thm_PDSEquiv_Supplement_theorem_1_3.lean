-- Prove2me | Theorems.Thm_PDSEquiv_Supplement_theorem_1_3
-- name    : PDSEquiv.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:50:58.68729+00:00
-- url     : https://prove2.me/theorems/49ec2a20-f62f-4fc7-9a1a-218e348695e5
-- title:
--   Theorem 1.3 — planted clique conjectures in the fixed-$k$ model are equivalent (clique finding, constant-advantage decision, optimality of edge counting)
-- statement:
--   Let $\mathrm{PDS}(n,k,1,1/2)$ be the planted clique distribution (a uniformly random $k$-subset of $[n]$ is made a clique, every other pair is an edge with probability $1/2$) and $\mathrm{ER}(n,1/2)$ the uniform random graph on $[n]$. For a $\{0,1\}$-valued algorithm $A$ write its advantage as
--   $$
--   \bigl|\Pr_{A,\,G\sim\mathrm{PDS}(n,k,1,1/2)}[A(G)=1]-\Pr_{A,\,G\sim\mathrm{ER}(n,1/2)}[A(G)=1]\bigr|.
--   $$
--   The following three statements are equivalent.
--
--   1. **(Planted clique conjecture.)** For every constant $\alpha\in(0,1/2)$ and every randomized polynomial-time algorithm $A$, for all large $n$, with $k=\lfloor n^{1/2-\alpha}\rfloor$,
--   $$\Pr_{A,\,G\sim\mathrm{PDS}(n,k,1,1/2)}\bigl[A(G)\text{ is a }k\text{-clique of }G\bigr]<\tfrac12 .$$
--   2. **(Fixed-$k$ decision.)** For every constant $\alpha\in(0,1/2)$, every $\varepsilon>0$ and every randomized polynomial-time algorithm $A$, for all large $n$, with $k=\lfloor n^{1/2-\alpha}\rfloor$, the advantage of $A$ between $\mathrm{PDS}(n,k,1,1/2)$ and $\mathrm{ER}(n,1/2)$ is $<\varepsilon$.
--   3. **(Optimality of edge counting.)** For every constant $\alpha\in(0,1/2)$, every $\varepsilon>0$ and every randomized polynomial-time algorithm $A$ with $O(\log n)$ bits of advice, for all large $n$ and **all** integers $2\le k\le n^{1/2-\alpha}$, the advantage of $A$ between $\mathrm{PDS}(n,k,1,1/2)$ and $\mathrm{ER}(n,1/2)$ is
--   $$<(1+\varepsilon)\,\frac{k(k-1)}{2\sqrt{\pi n(n-1)}} .$$
--
--   Edge counting achieves advantage $(1-o(1))\,k(k-1)/(2\sqrt{\pi n(n-1)})$ (Proposition 4.1), so (3) says that edge counting is optimal up to the factor $1+\varepsilon$, uniformly over the window of planted sizes. The theorem adds the fixed-$k$ decision conjecture and this sharp optimality to the equivalence class of the search version of the planted clique conjecture.
--
--   **Formalization Note** Algorithms are programs of the published machine `PDSEquiv.Machine`; "randomized polynomial-time" is `PolyTimeAlg` (no oracle, cost $(N+2)^c$ on every branch for every graph), and an algorithm with advice is `PolyTimeAdviceAlg` from `PDSEquiv.Supplement.Advice` together with an arbitrary advice sequence of length at most $h\lceil\log_2 n\rceil$. In (1) the event is that the output is the characteristic list of a set $T$ with $|T|=k$ whose distinct vertices are pairwise adjacent (any $k$-clique, not necessarily the planted one). An algorithm accepts when it outputs $[1]$. Probabilities are over the graph and the algorithm's coins. "For all large $n$" is "there is $n_0$ such that for all $n\ge n_0$", with $n_0$ chosen after $\alpha$, $\varepsilon$, the algorithm and its advice; in (3) the bound holds for every $k$ in the window at that $n$. $n^{1/2-\alpha}$ is the real power.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm → a program `A` of `PDSEquiv.Machine` with `PolyTimeAlg A`, run on the input `enc G`; reason: the paper names no machine; this is the base mission's published model, used for every algorithm of the paper.
--   - encoding: A finds a k-clique with probability 1/2; A cannot → the sum over G of PDS(n, k, 1, 1/2)-mass times the probability that A outputs the characteristic list of some T with |T| = k and T a clique of G, compared < 1/2; reason: "with probability ε" means probability ≥ ε (p.12), so "cannot" is < 1/2; a graph's law times the algorithm's output law is the joint probability.
--   - encoding: advantage ε in Section 1's normalization → |E_{PDS} acc − E_{ER} acc| < ε, acc G the probability of the output [1]; reason: Section 1's {0,1}-valued advantage, half of §4's adv (p.13); the threshold of (3) is written exactly as printed, k(k−1)/(2√(πn(n−1))) = Λ_n(k)/2.
--   - reading: algorithm with O(log n) bits of advice → one program A, a fixed h ∈ ℕ and an arbitrary sequence adv : ℕ → List Bool with |adv n| ≤ h·⌈log₂ n⌉, A running on enc G followed by |s| and the bits of s, polynomial time for every graph and every string s of that length (PolyTimeAdviceAlg); reason: the paper's own definition, Remark 8.3 (p.35) and the sentence after Corollary 1.2 (p.3).
--   - reading: in (3), A receives the graph and its advice → A does not receive k; reason: §4.1 "an algorithm receives the graph and any additional inputs explicitly specified in the statement"; the advice may encode a size k_n since it depends on n.
--   - encoding: for all large n ∈ ℕ → ∃ n₀, ∀ n ≥ n₀, n₀ chosen after α, ε, A, h and the advice sequence, and in (3) before k; reason: the standard reading of "for all large n" with the printed quantifier order.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Theorem 1.3, p.3 (PDF p.5); proof §B.6, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Supplement_Advice

set_option autoImplicit false

namespace PDSEquiv.Supplement

open PDSEquiv

open Classical in
/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Theorem 1.3, p.3 (PDF p.5); proof §B.6, p.43 (PDF p.45).
The following are equivalent.
(1) For any constant `α ∈ (0, 1/2)` and any randomized polynomial-time algorithm `A`, for all large `n`
and `k := ⌊n^{1/2−α}⌋`, `A` cannot find a `k`-clique in `PDS(n, k, 1, 1/2)` with probability `1/2`.
(2) For any constants `α ∈ (0, 1/2)`, `ε > 0` and any randomized polynomial-time algorithm `A`, for all
large `n` and `k := ⌊n^{1/2−α}⌋`, `A` cannot distinguish `PDS(n, k, 1, 1/2)` and `ER(n, 1/2)` with
advantage `ε`.
(3) For any constants `α ∈ (0, 1/2)`, `ε > 0` and any randomized polynomial-time algorithm `A` with
`O(log n)` bits of advice, for all large `n` and all integers `2 ≤ k ≤ n^{1/2−α}`, `A` cannot
distinguish `PDS(n, k, 1, 1/2)` and `ER(n, 1/2)` with advantage `(1 + ε) k(k−1)/(2√(πn(n−1)))`.

**Formalization Note.** The machine is `PDSEquiv.Machine`; a randomized polynomial-time algorithm is a
program with `PolyTimeAlg` (no oracle, log-cost `(N+2)^c` on every branch). An algorithm "finds a
`k`-clique" when its output is the characteristic list `charList T` of a set `T` with `|T| = k` that is
a clique of the input graph (any `k`-clique, not necessarily the planted one); every other output is a
failure. "With probability `1/2`" means probability `≥ 1/2` (p.12), so "cannot" is `< 1/2`. Advantage is
in Section 1's normalization, `|Pr_{PDS}[A = 1] − Pr_{ER}[A = 1]|` (half of §4's `adv`), acceptance
being the output `[1]`; "cannot distinguish with advantage `δ`" is `< δ`. "For all large `n`" is
`∃ n₀, ∀ n ≥ n₀`, with `n₀` chosen after `α`, `ε`, the algorithm and its advice. `O(log n)` bits of
advice is Remark 8.3: a fixed `h`, an arbitrary advice sequence `adv : ℕ → List Bool` with
`|adv n| ≤ h ⌈log₂ n⌉`, and one program running in polynomial time for every string of that length
(`PolyTimeAdviceAlg`). In (3) the algorithm receives the graph and the advice, not `k`. `α`, `ε` are
real; `n^{1/2−α}` is the real power. -/
theorem theorem_1_3 :
    List.TFAE
      [ ∀ α : ℝ, 0 < α → α < 1 / 2 → ∀ A : Program, PolyTimeAlg A →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
            expect (pdsMass n ⌊(n : ℝ) ^ (1 / 2 - α)⌋₊ 1 (1 / 2))
                (fun G => ∑ T : Finset (Fin n),
                  if T.card = ⌊(n : ℝ) ^ (1 / 2 - α)⌋₊ ∧ IsCliqueSet G T then
                    outMass A noOracle (enc G) (charList T) else 0) < 1 / 2,
        ∀ α ε : ℝ, 0 < α → α < 1 / 2 → 0 < ε → ∀ A : Program, PolyTimeAlg A →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
            |expect (pdsMass n ⌊(n : ℝ) ^ (1 / 2 - α)⌋₊ 1 (1 / 2))
                (fun G => outMass A noOracle (enc G) acceptOut) -
              expect (erMass n (1 / 2)) (fun G => outMass A noOracle (enc G) acceptOut)| < ε,
        ∀ α ε : ℝ, 0 < α → α < 1 / 2 → 0 < ε →
          ∀ (A : Program) (h : ℕ) (adv : ℕ → List Bool),
            (∀ n, (adv n).length ≤ h * Nat.clog 2 n) → PolyTimeAdviceAlg A h →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ (n : ℝ) ^ (1 / 2 - α) →
            |expect (pdsMass n k 1 (1 / 2))
                (fun G => outMass A noOracle (adviceInput G (adv n)) acceptOut) -
              expect (erMass n (1 / 2))
                (fun G => outMass A noOracle (adviceInput G (adv n)) acceptOut)| <
              (1 + ε) * ((k : ℝ) * ((k : ℝ) - 1) / (2 * Real.sqrt (Real.pi * n * ((n : ℝ) - 1)))) ] := by sorry

end PDSEquiv.Supplement
