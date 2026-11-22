-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_5_25
-- name    : QuantumKtSoI.Supplement.theorem_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:43:05.225541+00:00
-- url     : https://prove2.me/theorems/8e9784ea-369a-45d2-b24d-060540733290
-- title:
--   Theorem 5.25, p.75 — no $2^{\eta|x|}(|x|+|w|+2)^{c_A}$-time machine separates $\mathrm{qKt}(x|w)\ge\beta|x|$ from $\mathrm{qKt}(x|w)\le\alpha|x|$
-- statement:
--   Fix reals $0<\alpha<\beta<1$ and an integer $c_A\ge1$. There is $\eta>0$ for which there do not exist a machine $A$ and an integer $n_A$ satisfying the following for every pair of strings $x,w$ with $|x|\ge n_A$: the machine $A$ halts on $\langle x,w\rangle$ within
--   $$2^{\eta|x|}(|x|+|w|+2)^{c_A}$$
--   steps; it accepts with probability at least $2/3$ if $\mathrm{qKt}(x|w)\ge\beta|x|$, and rejects with probability at least $2/3$ if $\mathrm{qKt}(x|w)\le\alpha|x|$. Accepting means outputting the string $1$, and rejecting means outputting any other string.
--
--   This is the exponential hardness of estimating conditional quantum Kt complexity.
--
--   **Formalization Note** The values of $\mathrm{qKt}$ are read in $\mathbb R$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
--   - encoding: rejects with probability at least 2/3 → accepts (outputs the string 1) with probability at most 1/3; reason: the machine has halted on every branch, so its output probabilities sum to one (Lemma 3.3(ii))
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 5.25, p.75

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 5.25** (Exponential hardness of estimating conditional quantum Kt complexity;
Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.75). Fix reals `0 < α < β < 1` and an integer `c_A ≥ 1`. There is `η > 0` for which there
do not exist a machine `A` and an integer `n_A` such that, for every pair of strings `x, w` with
`|x| ≥ n_A`, `A` halts on `⟨x, w⟩` within `2^{η|x|}(|x|+|w|+2)^{c_A}` steps, accepts (outputs the
string `1`) with probability at least `2/3` if `qKt(x|w) ≥ β|x|`, and rejects (outputs any other
string) with probability at least `2/3` if `qKt(x|w) ≤ α|x|`.

**Formalization Note** `G` is any admissible glue routine set (p.24). Halting is on every branch,
by the real deadline read as `⌊·⌋` (p.22). Because `A` has halted on every branch, its output
probabilities sum to one (Lemma 3.3(ii)), so rejecting with probability at least `2/3` is written as
accepting with probability at most `1/3`. -/
theorem theorem_5_25 (G : GlueRoutines) (hG : G.Admissible) :
    ∀ α β : ℝ, 0 < α → α < β → β < 1 → ∀ cA : ℕ, 1 ≤ cA → ∃ η : ℝ, 0 < η ∧
      ¬∃ A : CodedMachine, A.Valid ∧ ∃ nA : ℕ, ∀ x w : List Bool, nA ≤ x.length →
        A.toMachine.HaltsWithin (pair x w)
            ⌊(2 : ℝ) ^ (η * x.length) * ((x.length : ℝ) + w.length + 2) ^ cA⌋₊ ∧
          (β * x.length ≤ (qKt G x w : ℝ) → (2 / 3 : ℝ) ≤ A.toMachine.outputProb (pair x w)
            ⌊(2 : ℝ) ^ (η * x.length) * ((x.length : ℝ) + w.length + 2) ^ cA⌋₊ [true]) ∧
          ((qKt G x w : ℝ) ≤ α * x.length → A.toMachine.outputProb (pair x w)
            ⌊(2 : ℝ) ^ (η * x.length) * ((x.length : ℝ) + w.length + 2) ^ cA⌋₊ [true] ≤ 1 / 3) := by sorry

end QuantumKtSoI.Supplement
