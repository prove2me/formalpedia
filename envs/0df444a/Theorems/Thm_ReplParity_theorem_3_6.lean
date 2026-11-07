-- Prove2me | Theorems.Thm_ReplParity_theorem_3_6
-- name    : ReplParity.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:50.237261+00:00
-- url     : https://prove2.me/theorems/7a047684-3a58-4742-b43e-0293d893e223
-- title:
--   Theorem 3.6 — a polynomial-time parity learner, $\rho$-replicable on every distribution, from $O(d^3/(\varepsilon\rho^2)+\log(1/\delta)/\varepsilon)$ samples
-- statement:
--   There are an absolute constant $C$, a sample size $m(d,\varepsilon,\delta,\rho)$, a seed length $R(d,\varepsilon,\delta,\rho)$ and a single learner $A$ such that:
--
--   1. $A$ runs in polynomial time: it is computed by a Turing machine (Mathlib's TM2 model) within a polynomial number of steps in the length of the binary encoding of its input $(d,\varepsilon,\delta,\rho,S,r)$;
--   2. the seed length $R$ is bounded by a polynomial in $d+m$ and the encoding lengths of $\varepsilon,\delta,\rho$;
--   3. for every $d\ge1$ and all rationals $0<\varepsilon,\delta,\rho<1$, with the seed $r$ uniform on $\{0,1\}^R$:
--      - the sample size satisfies
--   $$m\le C\Big(\frac{d^3}{\varepsilon\rho^2}+\frac{\log(1/\delta)}{\varepsilon}\Big);$$
--      - every output is $\bot$ or a parity $f_z$, $z\in\mathbb F_2^d$;
--      - $A$ is $\rho$-replicable on every labeled distribution on $\mathbb F_2^d\times\{0,1\}$ (Definition 2.1);
--      - $A$ is realizably $(\varepsilon,\delta)$-PAC for parities (Definition 2.2);
--      - on every sample consistent with some parity, $A$ outputs a parity (never $\bot$), for every seed.
--
--   This is the formal version of the paper's Theorem 1.1: the previous efficient replicable parity learner needed $d^6\log(1/\rho)/(\varepsilon^2\rho^2)$ samples.
--
--   Differences from the source:
--   - reading: polynomial-time finite-bit learner (§2.2) → Nonempty (Turing.TM2ComputableInPolyTime encIn encOut A) for one total function A on the fixed binary encoding of (d, ε, δ, ρ, sample, seed bits); reason: polynomial time is invariant under polynomial simulation; the encoding is binary and unpadded, so polynomial in its length is polynomial in the sample size, the dimension and the parameters' encoding lengths (paper.md decision 3)
--   - reading: the seed is a string of unbiased bits → a uniform string of R(d, ε, δ, ρ) bits with R ≤ c·(d + m + sizes of ε, δ, ρ)^k + c; reason: without a polynomial bound a long seed would weaken the time clause (paper.md decision 3)
--   - reading: For every d ≥ 1 and all 0 < ε, δ, ρ < 1, there is a polynomial-time learner → C, m, R and A are chosen before d, ε, δ, ρ: one machine takes the parameters as input; reason: for fixed parameters the input set is finite, so a per-instance learner would make polynomial time vacuous; this is the stronger reading, the one of Figure 2 (paper.md decision 4)
--   - encoding: O(·) → ∃ C before every other quantifier; reason: §2, p.10: constants inside O(·) are absolute
--   - encoding: outputs are parities or ⊥, compared exactly → the raw output is none or a bit list of length d, read as z ∈ 𝔽ᵈ₂ naming f_z; replicability compares the decoded z; reason: z ↦ f_z is injective, so comparing z's compares parities (paper.md decision 9)
--   - encoding: rational parameters, labels {0,1}, labeled distributions on the finite domain 𝔽ᵈ₂ × {0,1} → ε, δ, ρ : ℚ; labels in 𝔽₂; every PMF on 𝔽ᵈ₂ × 𝔽₂ (real weights); probabilities as finite sums; reason: same objects (paper.md decision 5)
--   - reading: it never outputs ⊥ on a sample consistent with some parity → for every such sample and every seed; reason: "never" quantifies over all runs; the proof gives containment for every seed (paper.md decision 9)
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Theorem 3.6, p.19 (PDF p.21) (formal version of Theorem 1.1, pp.1–2)

import Mathlib
import Definitions.Def_ReplParity_parity
import Definitions.Def_ReplParity_IsReplicable
import Definitions.Def_ReplParity_IsRealizablyPAC
import Definitions.Def_ReplParity_runLearner

namespace ReplParity

/-- **Theorem 3.6 (Formal version of Theorem 1.1): a polynomial-time parity learner, ρ-replicable on
every labeled distribution, from O(d³/(ερ²) + log(1/δ)/ε) samples.** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), Theorem 3.6, p.19 (PDF p.21): "For every d ≥ 1 and all 0 < ε, δ, ρ < 1, there is
a polynomial-time finite-bit learner for parities over 𝔽ᵈ₂ with m = O(d³/(ερ²) + log(1/δ)/ε)
samples. Its outputs are parities or ⊥, it is ρ-replicable on every labeled distribution and
realizably (ε, δ)-PAC, and it never outputs ⊥ on a sample consistent with some parity."

There are an absolute constant `C`, a sample size `m(d, ε, δ, ρ)`, a seed length `R(d, ε, δ, ρ)`
and one total function `A` on machine inputs such that:
1. `A` is computed in polynomial time by a Mathlib `TM2` machine on the fixed binary encodings
   `encIn`, `encOut`;
2. `R` is bounded by a polynomial in `d + m + (encoding lengths of ε, δ, ρ)`;
3. for every `d ≥ 1` and rationals `0 < ε, δ, ρ < 1`, with `m = m(d, ε, δ, ρ)`, `R = R(d, ε, δ, ρ)`
   and the seed uniform on `R`-bit strings:
   * `m ≤ C (d³/(ερ²) + log(1/δ)/ε)`;
   * every output is `⊥` or a bit vector of length `d` (a parity `f_z`);
   * the learner is ρ-replicable on every labeled distribution (Definition 2.1);
   * it is realizably (ε, δ)-PAC for the class of parities (Definition 2.2);
   * on a sample consistent with some parity it outputs a parity, for every seed.

**Formalization Note.** One machine serves every `d, ε, δ, ρ` (they are part of its input), and `C`,
`m`, `R`, `A` are chosen before `d, ε, δ, ρ`; otherwise "polynomial-time" would be vacuous on the
finite input set of fixed parameters. -/
theorem theorem_3_6 :
    ∃ C : ℝ, ∃ m R : ℕ → ℚ → ℚ → ℚ → ℕ, ∃ A : LInput → Option (List Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encIn encOut A) ∧
      (∃ k c : ℕ, ∀ (d : ℕ) (ε δ ρ : ℚ),
        R d ε δ ρ ≤ c * (d + m d ε δ ρ + ratSize ε + ratSize δ + ratSize ρ) ^ k + c) ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε δ ρ : ℚ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → 0 < ρ → ρ < 1 →
        ((m d ε δ ρ : ℝ) ≤ C * ((d : ℝ) ^ 3 / ((ε : ℝ) * (ρ : ℝ) ^ 2) + Real.log (1 / (δ : ℝ)) / ε)) ∧
        (∀ (S : Fin (m d ε δ ρ) → Example d) (r : Fin (R d ε δ ρ) → Bool),
          runLearner A d ε δ ρ S r = none ∨
            ∃ l : List Bool, runLearner A d ε δ ρ S r = some l ∧ l.length = d) ∧
        IsReplicable (fun (S : Fin (m d ε δ ρ) → Example d) (r : Fin (R d ε δ ρ) → Bool) =>
          learnerOutput A d ε δ ρ S r) (ρ : ℝ) ∧
        IsRealizablyPAC (Set.range (parity (d := d)))
          (fun (S : Fin (m d ε δ ρ) → Example d) (r : Fin (R d ε δ ρ) → Bool) =>
            (learnerOutput A d ε δ ρ S r).map parity) (ε : ℝ) (δ : ℝ) ∧
        ∀ S : Fin (m d ε δ ρ) → Example d, (∃ z : Vec d, ∀ i, parity z (S i).1 = (S i).2) →
          ∀ r : Fin (R d ε δ ρ) → Bool, learnerOutput A d ε δ ρ S r ≠ none := by sorry

end ReplParity
