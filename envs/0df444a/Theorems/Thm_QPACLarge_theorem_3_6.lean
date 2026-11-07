-- Prove2me | Theorems.Thm_QPACLarge_theorem_3_6
-- name    : QPACLarge.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:03.695329+00:00
-- url     : https://prove2.me/theorems/13be4980-75a3-4bf7-942e-6e7468147455
-- title:
--   Theorem 3.6 — $Q^+(n,m)$ reaches agreement $1/2+(b/4)\sqrt{m/N}$ with probability $\ge1-C_0/m$
-- statement:
--   Let $b$ be a constant as in Lemma 3.5 and $C_0 = 4/b^2$. There are a polynomial $p$ and an amplified quantum learner $Q^+(n, m)$ such that for every $n \ge 1$, $N = 2^n$, and every odd $1 \le m \le N$: $Q^+(n, m)$ uses exactly $m$ independent quantum random examples, has at most $m\,p(n)$ gates, its description is printed from $(1^n, 1^m)$ within $m\,p(n)$ steps, and for every target $f : \{0,1\}^n \to \{0,1\}$ it outputs a Boolean circuit $h$ of size at most $m\,p(n)$ with
--
--   $$
--   \Pr_{Q^+}\Big[\Pr_{x\sim U_n}[h(x) = f(x)] \ge \frac12 + \frac b4\sqrt{\frac mN}\Big] \ge 1 - \frac{C_0}{m}.
--   $$
--
--   The paper's $Q^+(n,m)$ runs the quantum sampler $m$ times and outputs the majority of the $m$ measured quadratic hypotheses.
--
--   Differences from the source:
--   - reading: the specific learner $Q^+(n,m)$ (majority of $m$ runs of $Q$) → there exists a two-parameter family $Q^+$ with the stated resources and guarantee; reason: the theorem is used only through this guarantee; the paper's construction is the intended witness
--   - reading: "Let $b$ be the constant in Lemma 3.5" → every $b$ with the property of Lemma 3.5 (`IsMajorityBiasConst b`); reason: Lemma 3.5 asserts only existence, so "the constant" is any constant with that property
--   - encoding: a quantum algorithm running in time $T$ → a family of Clifford+T circuits on copies of $|\mathrm{QEX}_f\rangle$ plus ancillas, output read from designated wires, with at most $T$ gates and a machine printing its description (numbers and wire indices in binary) within $T$ steps, the output circuit in a binary prefix-free code; reason: the model of Section 2.3, p.16; the paper fixes no gate set or encoding, and binary codes keep a description of a size-$S$ object at $O(S\log S)$ bits, as running times count
--   - encoding: time and circuit size $m\cdot\mathrm{poly}(n)$ → $m\,p(n)$ for one polynomial $p \in \mathbb N[X]$ (gates, printing steps, output size); reason: the maximum of several polynomials is a polynomial
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 3.6, p.29

import Mathlib
import Definitions.Def_QPACLarge_QexFamily
import Definitions.Def_QPACLarge_QexFamily_code
import Definitions.Def_QPACLarge_QexFamily_gateCount
import Definitions.Def_QPACLarge_QexFamily_success
import Definitions.Def_QPACLarge_agreement
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_QPACLarge_IsMajorityBiasConst

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **Theorem 3.6 (Guarantee for the Amplified Learner).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 3.6, p.29: "Let `b` be the constant in Lemma 3.5, and set `C₀ = 4/b²`. For every
target `f ∈ ALLₙ` and every odd integer `1 ≤ m ≤ N`, `Q⁺(n, m)` uses exactly `m` independent quantum
random examples, runs in time `m · poly(n)`, and outputs a deterministic classical Boolean circuit
of size `m · poly(n)` such that `Pr_{Q⁺}[Pr_{x∼Uₙ}[h(x) = f(x)] ≥ 1/2 + (b/4)√(m/N)] ≥ 1 − C₀/m`."

**Formalization Note.** `Q⁺` is a two-parameter family of quantum learners (`QexFamily` over
`(n, m)`); it is asserted to exist, with one polynomial `p` bounding the gate count, the time a
machine `G` needs to print the description of `Q⁺(n, m)` from `(1ⁿ, 1^m)`, and the size of the output
circuit, each by `m · p(n)`. `b` is any constant with the property of Lemma 3.5. `N = 2ⁿ`, `n ≥ 1`. -/
theorem theorem_3_6 (b : ℝ) (hb : IsMajorityBiasConst b) :
    ∃ (p : Polynomial ℕ) (Q : QexFamily (ℕ × ℕ) Prod.fst) (G : Turing.TM2ComputableAux Bool Bool),
      ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, Odd m → m ≤ 2 ^ n →
        Q.ex (n, m) = m ∧ Q.gateCount (n, m) ≤ m * p.eval n ∧
        HMBinPacking.OutputsWithin G (encNat n ++ encNat m) (Q.code (n, m)) (m * p.eval n) ∧
        ∀ f : Qubits n → Bool,
          1 - 4 / b ^ 2 / (m : ℝ) ≤ Q.success (n, m) f (fun h => h.size ≤ m * p.eval n ∧
            1 / 2 + b / 4 * Real.sqrt ((m : ℝ) / 2 ^ n) ≤ agreement f fun x => h.eval x 0) := by sorry

end QPACLarge
