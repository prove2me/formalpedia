-- Prove2me | Theorems.Thm_QPACLarge_theorem_1_2_ii
-- name    : QPACLarge.theorem_1_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:10.725167+00:00
-- url     : https://prove2.me/theorems/fdd2eb52-411e-44ed-ae50-ca62c9b031ad
-- title:
--   Theorem 1.2 (ii) — agreement $1/2+(a_1/\sqrt\eta)2^{-n/2}$ with probability $\ge1-\eta$ in time $\mathrm{poly}(n)/\eta$
-- statement:
--   There are universal constants $a_1, C > 0$ and a quantum algorithm $Q^+$ such that, given $n \ge 1$ and $\eta \in (0, 1/2)$ with $\eta \ge C\cdot 2^{-n}$, $Q^+$ uses $O(1/\eta)$ independent quantum random examples of $f \in \mathrm{ALL}_n$, runs in time $T(n,\eta) = \mathrm{poly}(n)\cdot\frac1\eta$, and outputs a Boolean circuit $h$ of size at most $T(n,\eta)$ with
--
--   $$
--   \Pr_{Q^+}\Big[\mathrm{agreement}(f, h) \ge \frac12 + \frac{a_1}{\sqrt\eta}\cdot 2^{-n/2}\Big] \ge 1 - \eta .
--   $$
--
--   In the formal statement the algorithm is a family $Q^+(n, m)$ indexed by $n$ and the number $m \le c/\eta$ of examples, whose gate count, description time and output size are at most $p(n)/\eta$. This tradeoff between accuracy, confidence and time is what Theorem 1.5 applies to padded targets.
--
--   Differences from the source:
--   - reading: a quantum algorithm $Q^+$ given $n$ and the real $\eta$ → for each $(n,\eta)$ some index $(n, m)$, $m \le c/\eta$, of one uniform two-parameter family $Q^+(n,m)$; reason: the algorithm uses $\eta$ only through the number $m$ of examples it determines (p.30); a real number is not a finite input
--   - reading: the algorithm $Q^+$ → existence of a family with the stated resources and guarantee; reason: the theorem is used only through this guarantee
--   - encoding: a quantum algorithm running in time $T$ → a family of Clifford+T circuits on copies of $|\mathrm{QEX}_f\rangle$ plus ancillas, output read from designated wires, with at most $T$ gates and a machine printing its description (numbers and wire indices in binary) within $T$ steps, the output circuit in a binary prefix-free code; reason: the model of Section 2.3, p.16; the paper fixes no gate set or encoding, and binary codes keep a description of a size-$S$ object at $O(S\log S)$ bits, as running times count
--   - encoding: $O(1/\eta)$ examples, $T(n,\eta) = \mathrm{poly}(n)/\eta$ → $m \le c/\eta$; gates, output size $\le p(n)/\eta$, printing within $\lfloor p(n)/\eta\rfloor$ steps; reason: one constant $c$ and one polynomial $p$, quantified before $n$ and $\eta$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 1.2 (ii), p.5; proof in Section 3.3, Choosing the Failure Probability, p.30

import Mathlib
import Definitions.Def_QPACLarge_QexFamily
import Definitions.Def_QPACLarge_QexFamily_code
import Definitions.Def_QPACLarge_QexFamily_gateCount
import Definitions.Def_QPACLarge_QexFamily_success
import Definitions.Def_QPACLarge_agreement
import Definitions.Def_HMBinPacking_OutputsWithin

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **Theorem 1.2 Item (ii) (amplified quantum learner).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Theorem 1.2, p.5: "There are universal constants `a₀, a₁, C > 0` and `p⋆ > 1/2` such that the
following statements hold. … (ii) There is a quantum algorithm `Q⁺` that, given `n ∈ ℕ` and
`η ∈ (0, 1/2)` satisfying `η ≥ C · 2^{−n}`, and using `O(1/η)` independent quantum random examples
for `f ∈ ALLₙ`, runs in time `T(n, η) = poly(n) · 1/η` and outputs a deterministic classical Boolean
circuit `h` of size at most `T(n, η)` such that `Pr_{Q⁺}[agreement(f, h) ≥ 1/2 + (a₁/√η) · 2^{−n/2}]
≥ 1 − η`." (Proof: Section 3.3, "Choosing the Failure Probability", p.30.)

**Formalization Note.** `Q⁺` is a two-parameter family of quantum learners (`QexFamily` over
`(n, m)`), asserted to exist; `η` is supplied through the number `m ≤ c/η` of examples it
determines, so `(n, m)` is the index of the learner. `T(n, η) = p(n)/η` bounds the gate count, the
steps a machine `G` needs to print the description of `Q⁺(n, m)` from `(1ⁿ, 1^m)`, and the output
circuit's size. `n ≥ 1`. -/
theorem theorem_1_2_ii :
    ∃ a₁ C : ℝ, 0 < a₁ ∧ 0 < C ∧
      ∃ (c : ℝ) (p : Polynomial ℕ) (Q : QexFamily (ℕ × ℕ) Prod.fst)
        (G : Turing.TM2ComputableAux Bool Bool),
        ∀ n : ℕ, 1 ≤ n → ∀ η : ℝ, 0 < η → η < 1 / 2 → C * ((2 : ℝ) ^ n)⁻¹ ≤ η →
          ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ c / η ∧ Q.ex (n, m) = m ∧
            (Q.gateCount (n, m) : ℝ) ≤ (p.eval n : ℕ) / η ∧
            HMBinPacking.OutputsWithin G (encNat n ++ encNat m) (Q.code (n, m))
              ⌊((p.eval n : ℕ) : ℝ) / η⌋₊ ∧
            ∀ f : Qubits n → Bool,
              1 - η ≤ Q.success (n, m) f (fun h => (h.size : ℝ) ≤ (p.eval n : ℕ) / η ∧
                1 / 2 + a₁ / Real.sqrt η * (2 : ℝ) ^ (-(n : ℝ) / 2) ≤
                  agreement f fun x => h.eval x 0) := by sorry

end QPACLarge
