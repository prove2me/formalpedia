-- Prove2me | Theorems.Thm_QPACLarge_theorem_1_5
-- name    : QPACLarge.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:31.999352+00:00
-- url     : https://prove2.me/theorems/a2c7afdc-583c-463a-9fa0-486a1ccb057b
-- title:
--   Theorem 1.5 — quantum learners reach agreement $1/2+\lambda(n)$ in polynomial time; classical learners fail at $1/2+\lambda(n)/n^k$
-- statement:
--   Let $\lambda(n) > 0$ be constructive (Eq. (9)) with $n^{\omega(1)}\cdot 2^{-n/2} \le \lambda(n) \le n^{-\omega(1)}$, and let $k \ge 1$ be a real constant. Then:
--
--   1. There is a concept class $\mathcal C = \{\mathcal C_n\}_{n \ge 1}$ such that
--      - there is a polynomial-time quantum algorithm $A$ that, for every sufficiently large $n$ and every $f \in \mathcal C_n$, uses uniform quantum random examples and outputs a deterministic classical circuit $h$ with
--      $$\Pr_A\Big[\mathrm{agreement}(f, h) \ge \tfrac12 + \lambda(n)\Big] \ge 1 - \frac1{n^k};$$
--      - for every randomized membership-query learner $B$ making polynomially many queries, for every sufficiently large $n$ there is $f \in \mathcal C_n$ with
--      $$\Pr_B\Big[\mathrm{agreement}(f, h) \ge \tfrac12 + \frac{\lambda(n)}{n^k}\Big] \le \frac1{n^k}.$$
--   2. If subexponentially secure one-way functions exist, there is a concept class $\mathcal C \subseteq \mathrm{SIZE}[\mathrm{poly}]$ with the same quantum guarantee and such that for every uniform randomized polynomial-time membership-query learner $B$, every sufficiently large $n$ has $f \in \mathcal C_n$ with $\Pr_B[\mathrm{agreement}(f,h) \ge \frac12 + \frac{\lambda(n)}{n^k}] \le \frac1{n^k}$.
--
--   This is an unconditional super-polynomial separation in the time complexity of PAC learning Boolean functions under the uniform distribution, at inverse superpolynomial advantage, and it is robust: the classical learners fail even at the smaller advantage $\lambda(n)/n^k$ with the much smaller success probability $1/n^k$.
--
--   **Formalization Note** $n^k$ is a real power. The quantum algorithm is one uniform family of Clifford+T circuits whose descriptions a polynomial-time machine prints from $1^n$. $\mathcal C \subseteq \mathrm{SIZE}[\mathrm{poly}]$ is one $c$ with every $f \in \mathcal C_n$ ($n \ge 1$) of circuit size at most $n^c + c$.
--
--   Differences from the source:
--   - reading: $n^{\omega(1)}\cdot 2^{-n/2} \le \lambda(n) \le n^{-\omega(1)}$ → for every $c \in \mathbb N$, eventually $n^c 2^{-n/2} \le \lambda(n)$ and $\lambda(n) \le n^{-c}$; reason: the standard meaning of $\omega(1)$ exponents
--   - reading: $\lambda$ constructive (p.6: computable from $1^n$ in time $\mathrm{poly}(n)$; footnote 6: an efficient approximation suffices, see Section 5) → Eq. (9) of Section 5 with $s(n)$ output in binary by a polynomial-time machine; reason: footnote 6 defers to the formal definition of p.34; Eq. (9) asks less than computing $\lambda$, so it covers every $\lambda$ of the p.6 sentence
--   - generalization: every randomized membership-query polynomial-time learner $B$ (unconditional bullet) → every family of randomized decision trees with polynomially many queries and arbitrary hypotheses; reason: a polynomial-time learner with fixed coins is a decision tree with polynomially many queries, and its output circuit determines a hypothesis
--   - encoding: a quantum algorithm running in time $T$ → a family of Clifford+T circuits on copies of $|\mathrm{QEX}_f\rangle$ plus ancillas, output read from designated wires, with at most $T$ gates and a machine printing its description (numbers and wire indices in binary) within $T$ steps, the output circuit in a binary prefix-free code; reason: the model of Section 2.3, p.16; the paper fixes no gate set or encoding, and binary codes keep a description of a size-$S$ object at $O(S\log S)$ bits, as running times count
--   - encoding: randomized membership-query polynomial-time learner (conditional bullet) → the published `mqRun` learner with polynomial-time next-step function, $p(n)$ rounds and $\mathrm{rb}(n)$ coins, outputting a circuit code; reason: the next-step function recomputes the learner's state from the coins and the query history in polynomial time
--   - encoding: subexponentially secure one-way functions (p.19) → `SubexpOWFExists`: clocked Turing-machine inverters with $\lfloor 2^{n^\varepsilon}\rfloor$ steps and coins, positive polynomials as $p+1$; reason: clocking changes the adversary class only polynomially in the time bound, absorbed by the existential $\varepsilon$
--   - encoding: $\mathcal C \subseteq \mathrm{SIZE}[\mathrm{poly}]$; real $k$ → one $c$ with circuit size $\le n^c + c$ for $n \ge 1$; $n^k$ as `Real.rpow`; reason: the meaning of polynomial size; $k$ is an arbitrary real constant $\ge 1$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 1.5, p.7 (constructivity: Section 5, p.34, Eq. (9); proof: Section 5, pp.33–38)

import Mathlib
import Definitions.Def_QPACLarge_IsConstructive
import Definitions.Def_QPACLarge_QexFamily
import Definitions.Def_QPACLarge_QexFamily_code
import Definitions.Def_QPACLarge_QexFamily_success
import Definitions.Def_QPACLarge_agreement
import Definitions.Def_QPACLarge_treeSuccess
import Definitions.Def_QPACLarge_mqSuccess
import Definitions.Def_QPACLarge_InSIZE
import Definitions.Def_QPACLarge_SubexpOWFExists

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Learning Filter

/-- **Theorem 1.5 (Robust Quantum PAC Learning Advantage at Inverse Superpolynomial Correlation).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 1.5, p.7: "Let `λ(n)` be any constructive function satisfying
`n^{ω(1)} · 2^{−n/2} ≤ λ(n) ≤ n^{−ω(1)}`, and let `k ≥ 1` be an arbitrary constant. Then there is a
concept class `C = {Cₙ}_{n≥1}` for which the following holds. • There is a quantum algorithm `A`
that, for every sufficiently large `n` and every `f ∈ Cₙ`, uses quantum random examples, runs in
`poly(n)` time, and outputs a deterministic classical circuit `h` satisfying
`Pr_A[agreement(f, h) ≥ 1/2 + λ(n)] ≥ 1 − 1/nᵏ`. • For every randomized membership-query
polynomial-time learner `B`, for every sufficiently large `n` there is `f ∈ Cₙ` such that
`Pr_B[agreement(f, h) ≥ 1/2 + λ(n)/nᵏ] ≤ 1/nᵏ`. Moreover, if subexponentially secure one-way
functions exist, the concept class `C` can be chosen to satisfy `C ⊆ SIZE[poly]`."

The conclusion has two parts. (I) A class with the quantum bullet and the classical bullet, the
latter against every family of randomized membership-query learners making polynomially many
queries. (II) If subexponentially secure OWFs exist, a class inside `SIZE[poly]` with the quantum
bullet and the classical bullet against every uniform randomized polynomial-time membership-query
learner.

**Formalization Note.** `λ` is positive and constructive in the sense of Eq. (9), p.34
(`IsConstructive`); `n^{ω(1)} · 2^{−n/2} ≤ λ(n)` is: for every `c`, eventually
`n^c 2^{−n/2} ≤ λ(n)`, and `λ(n) ≤ n^{−ω(1)}` is: for every `c`, eventually `λ(n) ≤ n^{−c}`. `k` is
real and `nᵏ` is `Real.rpow`. The quantum algorithm is one family of Clifford+T circuits on copies of
`|QEX_f⟩` (`QexFamily`) whose descriptions a polynomial-time machine prints from `1ⁿ`, so its gate
count and number of examples are polynomial. In (I) the classical learners are randomized decision
trees (`treeSuccess`); in (II) they are the published `mqRun` learners with a polynomial-time
next-step function, `p(n)` rounds and `rb(n)` coins (`mqSuccess`). `C ⊆ SIZE[poly]` is: one `c`
with every `f ∈ Cₙ` (`n ≥ 1`) of circuit size at most `n^c + c`. -/
theorem theorem_1_5 (lam : ℕ → ℝ) (k : ℝ) (hpos : ∀ n, 0 < lam n) (hcons : IsConstructive lam)
    (hlow : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ lam n)
    (hup : ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, lam n ≤ (n : ℝ) ^ (-(c : ℝ))) (hk : 1 ≤ k) :
    (∃ C : (n : ℕ) → Set (Qubits n → Bool),
      (∃ L : QexFamily ℕ (fun n => n),
        (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n : ℕ, g (unary n) = L.code n) ∧
        ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ f ∈ C n,
          1 - 1 / (n : ℝ) ^ k ≤
            L.success n f (fun h => 1 / 2 + lam n ≤ agreement f fun x => h.eval x 0)) ∧
      ∀ (q : Polynomial ℕ) (R : (n : ℕ) → RandDecisionTree (Qubits n) Bool (Qubits n → Bool)),
        (∀ n, RandMakesAtMost (R n) (q.eval n)) →
        ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ f ∈ C n,
          treeSuccess (R n) f (fun h => 1 / 2 + lam n / (n : ℝ) ^ k ≤ agreement f h) ≤
            1 / (n : ℝ) ^ k) ∧
    (SubexpOWFExists →
      ∃ C : (n : ℕ) → Set (Qubits n → Bool),
        (∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ f ∈ C n, InSIZE f (n ^ c + c)) ∧
        (∃ L : QexFamily ℕ (fun n => n),
          (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n : ℕ, g (unary n) = L.code n) ∧
          ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ f ∈ C n,
            1 - 1 / (n : ℝ) ^ k ≤
              L.success n f (fun h => 1 / 2 + lam n ≤ agreement f fun x => h.eval x 0)) ∧
        ∀ (p rb : Polynomial ℕ) (g : Str → Str), PolyTimeComputable g →
          ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ f ∈ C n,
            mqSuccess g p rb n f (fun h => 1 / 2 + lam n / (n : ℝ) ^ k ≤ agreement f h) ≤
              1 / (n : ℝ) ^ k) := by sorry

end QPACLarge
