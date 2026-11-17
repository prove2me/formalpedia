-- Prove2me | Theorems.Thm_QaryCVP_Supplement_theorem_G_2
-- name    : QaryCVP.Supplement.theorem_G_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:17:47.030844+00:00
-- url     : https://prove2.me/theorems/ee74c4b1-08b5-47c6-9106-f976ea94565b
-- title:
--   Theorem G.2 — the infimum of the SVP objective (45) lies in $[0.2740094,0.27400949)$, and the rule (46) gives time $2^{0.27400949n+o(n)}$, space $2^{0.261392024n+o(n)}$
-- statement:
--   Consider the complete time objective (45) of the SVP construction on $0\le\delta\le1$, over every fixed decomposition depth $k\ge1$, every exact-search cutoff $\delta_0\in(1/2,1)$, tolerances $\varepsilon,\eta>0$, and an equation rate $\rho$ and proportions $t_0,\dots,t_k$ that may depend on the input density (through the counting parameter $a$, which satisfies $H(p_a)=\delta+o(1)$), subject to the coordinate conditions (3), the equation conditions (5), the even-modulus conditions (8) and the padding condition (72) $t_0H(p_a)/\rho>p_a(1)+\varepsilon$, all strict constraints holding with one uniform positive margin throughout $\delta_0\le H(p_a)\le1$.
--
--   1. The infimum of the objective over this family lies in $[0.2740094,\,0.27400949)$: every feasible choice has objective at least $0.2740094$, and some feasible choice has objective below $0.27400949$.
--   2. With the constants (46), $n_0=\lceil n/(1-\kappa)\rceil$ and the proportions (34), Algorithm 4 runs in time $2^{0.27400949n+o(n)}$ and space $2^{0.261392024n+o(n)}$ on every input with $q\ge2$, $n\ge1$, $m\ge0$, $\delta\le1$, omitting factors polynomial in the binary input length.
--
--   Part 1 says that the chosen three-step rule is within $9\cdot10^{-8}$ of the best time exponent provable by this parameterized construction (not of arbitrary SVP algorithms).
--
--   **Formalization Note** In part 2 the enumeration is a program computing a procedure $R$ that has the uniform bound of Lemma 3.2 on omitting a fixed vector at the rule's parameters; the program implementing Algorithm 4 outputs, on every coin tape, the model's output at a measurable assignment of the random choices whose law is within total-variation distance $2^{-n}$ of the model's law.
--
--   Differences from the source:
--   - encoding: its infimum lies in [0.2740094, 0.27400949) → every feasible choice has obj45 ≥ 0.2740094, and some feasible choice has obj45 < 0.27400949; reason: equivalent to the infimum lying in the half-open interval; avoids the junk value of sInf of an empty set
--   - reading: parameters that may depend on the input density, selected deterministically from the input dimensions and the counted radius → ρ and t₀, …, t_k as arbitrary functions of the counting parameter a; reason: the limiting form used by (45), where the cost is a function of a with H(p_a) = δ + o(1)
--   - reading: all strict constraints hold with uniform positive margins throughout δ0 ≤ H(p_a) ≤ 1 → one margin µ > 0 with ρ ≥ µ, µ ≤ tᵢ ≤ 1/2 − µ, (5), (8) and (72) each holding with slack µ for every a in the range; (3) non-strict; reason: one common margin is equivalent to a positive margin for each of finitely many constraints; (3) is non-strict as printed on p.15
--   - encoding: the maxima and suprema of (45) → real sSup of the images; reason: the w-range is a nonempty compact interval and the bracket is bounded on a feasible choice (ρ ≥ µ, bounded entropies), so sSup is the page's value
--   - generalization: δ0 ∈ (1/2, 1) and ε, η > 0 (rational in §5.1) → real δ0, ε, η in these ranges; reason: the lower bound over a larger family implies it over the rational one; the upper witness (46) is rational
--   - reading: Algorithm 4 (a specific procedure) has the stated time and space → there is a program Pr whose output on every coin tape equals the model alg4's output at φ(τ), for a measurable assignment φ of its random choices whose law under fair coins is within total-variation distance 2^{-n} of the model's law (ImplementsAlg4), with the stated bounds; reason: base decisions 3 and 4; the equal-output clause ties the cost to Algorithm 4, so neither a trivial program nor a derandomized run on one unlucky assignment can satisfy it; the law is required only up to total-variation 2^{-n}, not exactly, because fair bits cannot sample Z/qZ exactly (Section E.6.4, error 2^{-Ω(n²)} per sample)
--   - reading: the exact search of Algorithm 2, b̂p computed as in E.6.1, the outward intervals of E.6.2 → existential: some nonzero exact search meeting Definition 3.4, some b̂p with 0 ≤ b̂p − p_a(1) ≤ min{n⁻², 10⁻¹²}, some enclosures of width ≤ 1, all used by Pr; reason: these subprocedures are internal to Algorithm 4; their stated specifications are what the theorem and its cost use
--   - reading: the enumeration of Section 3.1 (Algorithm 1 / Algorithm 7) run with the rule's constants → ∃ a program Rprog computing a procedure R (ComputesEnum) that has, for every accurate b̂p, the uniform Lemma 3.2 omission bound at the rule's completion parameters under fair coins (InclusionBound); reason: the paper's enumeration has this bound by Lemma G.1 and §3.1.1 (p.106); requiring it excludes a trivial enumeration, so the cost claim is about the algorithm of Theorem 5.7
--   - encoding: δ = m log q / n ≤ D → the real density m log₂ q / n ≤ D (QaryCVP.density); reason: the same condition; D is a real constant
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: base decision 1 (R1); this machine charges bit operations at least as heavily
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13 (base R2)
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input, shared by time and space; reason: p.13 asymptotic convention (base R3); one g is the stronger form
--   - reading: Input: H ∈ (Z/qZ)^{m×n} → the input word n, m, q, then the entries of H row by row as canonical representatives in [0, q) (encSVP); reason: base R9 without a target
--   - reading: on every input (every execution) → the run halts on every coin tape and the bounds hold on every tape; reason: p.13 and Theorem 5.9 "Every execution" (base R10)
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem G.2, p.111 (PDF 112); (45) and (46), p.56; G.1, (72), p.104; (34), p.49; Lemma G.1, p.105

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_Supplement_svpBasics
import Definitions.Def_QaryCVP_Supplement_thetaDist
import Definitions.Def_QaryCVP_Supplement_svpExponents
import Definitions.Def_QaryCVP_Supplement_alg4

open MeasureTheory Filter Topology TwMSOCount.Main

namespace QaryCVP.Supplement

/-- **Theorem G.2** (the SVP objective on `0 ≤ δ ≤ 1` and the rule (46)). Kim, Kwon, Lee, Lee, STOC
2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem G.2, p.111; (45), p.56; (46), p.56;
(72), p.104; (34), p.49.

1. Consider the complete time objective (45) over every choice of a fixed depth `k ≥ 1`, an
   exact-search cutoff `δ₀ ∈ (1/2, 1)`, tolerances `ε, η > 0`, and an equation rate and proportions
   depending on the counting parameter `a` (equivalently on the input density), subject to (3), (5),
   (8) and the padding condition (72), every strict constraint holding with one uniform positive
   margin throughout `δ₀ ≤ H(p_a) ≤ 1`. Its infimum lies in `[0.2740094, 0.27400949)`: every
   feasible choice has objective at least `0.2740094`, and some feasible choice has objective below
   `0.27400949`.
2. With the constants (46), `n₀ = ⌈n/(1 − κ)⌉` and the proportions (34), Algorithm 4 runs in time
   `2^{0.27400949n + o(n)}` and space `2^{0.261392024n + o(n)}` on every input with `q ≥ 2`, `n ≥ 1`,
   `m ≥ 0`, `δ ≤ 1`: there are an enumeration program `Rprog` computing a procedure `R` that has the
   uniform fixed-vector bound of Lemma 3.2 at the rule's parameters (for every accurate `b̂p`), and an
   accurate `b̂p`, valid enclosures, a nonzero exact search and a program `Pr` implementing
   Algorithm 4 with them, whose every execution is within these bounds (up to a polynomial in the
   binary input length).

**Formalization Note.** Part 1 states the infimum through its two defining properties (lower bound
for every feasible choice; a feasible choice below the upper bound), which is equivalent to
`inf ∈ [0.2740094, 0.27400949)` and avoids the junk value of `sInf ∅`. The parameters "selected
deterministically from the input dimensions and the counted radius" are functions of `a`, the
limiting form used by (45). Part 2: the enumeration and the program are existential, `R` constrained
by the omission bound it must have for Theorem 5.7 (so that a trivial `R` cannot be used); `Pr`'s
output equals the model's at a measurable assignment of the random choices whose law is within
total variation `2^{−n}` of the model's (`ImplementsAlg4`). Machine,
`o(n)` and polynomial factors as in R1–R3. Decimals are exact rationals. -/
theorem theorem_G_2 :
    ((∀ C : Choice45, Feasible45 C → (2740094 / 10 ^ 7 : ℝ) ≤ obj45 C) ∧
      (∃ C : Choice45, Feasible45 C ∧ obj45 C < 27400949 / 10 ^ 8)) ∧
    ∃ (Rprog : Program) (R : EnumProc (ℕ → Bool)),
      ComputesEnum rule46 1 Rprog R ∧
      (∀ bp : ℕ → ℕ → ℕ → ℚ, BpAccurate bp → InclusionBound rule46 bp 1 coinTape R) ∧
      ∃ (bp : ℕ → ℕ → ℕ → ℚ) (encl : Encl) (E0 : SearchProc),
        BpAccurate bp ∧ EnclValid rule46 encl ∧ NonzeroSearchSpec E0 ∧
        ∃ (Pr : Program) (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
          ∀ n m q : ℕ, 1 ≤ n → 2 ≤ q → density q m n ≤ 1 →
            ∀ H : Matrix (Fin m) (Fin n) (ZMod q),
              RunsWithin Pr (encSVP H)
                ((2 : ℝ) ^ (27400949 / 10 ^ 8 * n + g n) * polyF K (encSVP H))
                ((2 : ℝ) ^ (261392024 / 10 ^ 9 * n + g n) * polyF K (encSVP H)) ∧
              ImplementsAlg4 Pr rule46 bp encl R E0 H := by sorry

end QaryCVP.Supplement
