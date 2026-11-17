-- Prove2me | Theorems.Thm_ReplParity_Supplement_theorem_5_3
-- name    : ReplParity.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:59:43.080285+00:00
-- url     : https://prove2.me/theorems/3132e2f2-0d00-4b94-bfca-58ac82c7221c
-- title:
--   Theorem 5.3 — learning $P_n$ at rate $n^2\,\mathrm{polylog}/(\varepsilon\rho^2)$ replicably $\iff$ near-isoperimetric robust IAT generators $\iff$ the same learners, replicable on every distribution
-- statement:
--   The following three statements are equivalent.
--
--   1. There are a constant $C$, a fixed polynomial bound on the logarithmic factors, and one polynomial-time finite-bit algorithm such that for every $n\ge1$ and all rationals $0<\varepsilon,\delta,\rho<1/2$ it is a learner for $P_n$ (all functions $[n]\to\{0,1\}$) with
--   $$m\le\frac{Cn^2}{\varepsilon\rho^2}\,\mathrm{polylog}(n,1/\varepsilon,1/\rho)+\frac{C\log(1/\delta)}{\varepsilon}$$
--   samples, which is realizably $(\varepsilon,\delta)$-PAC and $\rho$-replicable on realizable distributions.
--   2. There are a constant $C$, a fixed polynomial bound on the logarithmic factors, and a uniform efficient robust IAT generator (Definition 2.5) that, for every $N\ge1$ and all rationals $0<\gamma,\zeta<1/2$, outputs, except with probability $\zeta$, a robust description (Definition 2.4) of a $(\gamma,A)$-IAT (Definition 2.3) of $\mathbb R^N$ with
--   $$A\le CN\,\mathrm{polylog}(N,1/\gamma,1/\zeta).$$
--   3. The learners of statement 1 exist with $\rho$-replicability on every labeled distribution.
--
--   Here $\mathrm{polylog}(x_1,\dots,x_k)$ is $(1+\log x_1+\dots+\log x_k)^k$ up to the constant, a polynomial in the logarithms.
--
--   This characterizes the optimal quadratic rate of efficient replicable learning of $P_n$ by the existence of efficiently computable near-isoperimetric tilings, and shows that replicability on realizable distributions at this rate already gives replicability on every distribution.
--
--   **Formalization Note** Each statement carries its own constant $C$ and its own polylog exponent. Algorithms are Mathlib Turing machines that run in polynomial time on fixed binary encodings, one machine for all parameters.
--
--   Differences from the source:
--   - reading: "There is an absolute constant C and a fixed polynomial bound on the logarithmic factors such that the following three statements are equivalent" (one C, one polylog for all three) → each statement is an existential with its own C and exponent k, and the theorem is the equivalence of the three; reason: the proof (Corollary 4.5 via Lemma 4.1 and Propositions 4.3–4.4, Lemma 5.2 with m = O(A²/(ερ²) + …)) changes C and the polylog degree between statements, the informal Theorem 1.2 states the equivalence without a shared constant, and with a shared constant each side is an open existence question the paper does not settle; neither reading implies the other
--   - encoding: polylog(n, 1/ε, 1/ρ), a fixed polynomial in log n, log(1/ε), log(1/ρ) → (1 + log n + log(1/ε) + log(1/ρ))^k with the coefficients in C (likewise for polylog(N, 1/γ, 1/ζ)); reason: the logarithms are nonnegative in the parameter range, so the two classes of bounds coincide up to the existential constant
--   - reading: "uniform polynomial-time finite-bit learner" → one total function computed by a Mathlib TM2 machine in polynomial time on the base mission's fixed binary encoding (sample point (i, b) written as the example (e_i, b)), seed of polynomially many uniform bits, outputs ⊥ or an n-bit truth table; reason: the paper fixes no machine; same reading as the published goal Theorem 3.6
--   - reading: generator time "polynomial in N, 1/γ, and log(1/ζ)", query time polynomial in these and the encoding length of q → TM2 polynomial time on encodings carrying N + ⌈1/γ⌉ + ⌈log₂(1/ζ)⌉ in unary, so also polynomial in the encoding lengths of γ, ζ, the description and the random bits; random-bit counts polynomial; reason: §2.2 makes polynomial time include the encoding lengths of the parameters, and the machine must read its input
--   - reading: "finite-bit membership program" of a description → a bit string d run by a fixed query program Q that belongs to the generator and also receives N, γ, ζ; reason: the paper does not say how a description is executed; this is the standard reading of a generator outputting a program
--   - reading: "piecewise smooth boundaries" (undefined) → the boundary lies in finitely many C¹ images of compact subsets of ℝ^{N−1}; "surface area" H^{N−1} → the normalized (N−1)-dimensional Hausdorff measure on Euclidean ℝ^N; reason: standard meaning, and the one the flux formula of Lemma 5.1 uses; Mathlib's unnormalized Hausdorff measure would change A by an N-dependent factor
--   - encoding: a tiling {S_a} labeled by points a ∈ ℝ^N → a countable label set L ⊆ ℝ^N with a tile map a ↦ T a; dyadic query vectors → lists of N rationals with power-of-two denominators; volumes as outer measures in [0, ∞]; reason: Lean representation of the same objects
--   - encoding: "a (γ, A)-IAT with A ≤ C N polylog" → a (γ, C N (1 + log N + log(1/γ) + log(1/ζ))^k)-IAT; reason: the surface condition is an upper bound, so a (γ, A)-IAT with A below the bound is a (γ, bound)-IAT
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Theorem 5.3, p.26 (PDF p.28) (= Theorem 1.2, pp.2-3); Definitions 2.3-2.5, pp.11-12 (PDF pp.13-14)

import Mathlib
import Definitions.Def_ReplParity_Supplement_PnRateLearners
import Definitions.Def_ReplParity_Supplement_IsUniformIATGenerator

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- **Theorem 5.3 (Formal version of Theorem 1.2): replicable learning of `P_n` at the quadratic
rate ⟺ near-isoperimetric robust IAT generators ⟺ the same learners, replicable on every
distribution.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a Geometric
Characterization*, STOC 2027 submission (manuscript sha256 40424491…), Theorem 5.3, p.26
(PDF p.28): "There is an absolute constant C and a fixed polynomial bound on the logarithmic factors
such that the following three statements are equivalent.
1. For every n ≥ 1 and all rational 0 < ε, δ, ρ < 1/2, there is a uniform polynomial-time finite-bit
learner for P_n with m ≤ Cn²/(ερ²) polylog(n, 1/ε, 1/ρ) + C log(1/δ)/ε samples, which is realizably
(ε, δ)-PAC and ρ-replicable on realizable distributions.
2. For every N ≥ 1 and all rational 0 < γ, ζ < 1/2, a uniform efficient robust IAT generator
outputs, except with probability ζ, a robust description of a (γ, A)-IAT of ℝ^N with
A ≤ CN polylog(N, 1/γ, 1/ζ).
3. The learners of statement 1 exist with ρ-replicability on every labeled distribution."

The three propositions are
1. `PnRateLearners false`;
2. there are `C, k`, a generator `G` with `gbits` random bits and a query program `Q` with `qbits`
   random bits forming a uniform efficient robust IAT generator (Definition 2.5) with surface bound
   `A(N, γ, ζ) = C N (1 + log N + log(1/γ) + log(1/ζ))^k`;
3. `PnRateLearners true`;
and the theorem says they are equivalent.

**Formalization Note.** Each statement carries its own constant `C` and its own exponent `k` of the
logarithmic factor: the proof (Corollary 4.5, Lemma 5.2) changes both from one statement to the
next, and the informal Theorem 1.2 states the equivalence with no shared constant. The polylog
`polylog(N, 1/γ, 1/ζ)` is written `(1 + log N + log(1/γ) + log(1/ζ))^k` (nonnegative logs, the
constant absorbed into `C`). -/
theorem theorem_5_3 :
    List.TFAE
      [PnRateLearners false,
       ∃ C : ℝ, ∃ k : ℕ, ∃ (G : GenInput → GenOutput) (gbits : ℕ → ℚ → ℚ → ℕ)
         (Q : QInput → Option (List ℚ)) (qbits : ℕ → ℚ → ℚ → ℕ → ℕ),
         IsUniformIATGenerator G gbits Q qbits (fun N γ ζ =>
           C * (N : ℝ) * (1 + Real.log N + Real.log (1 / (γ : ℝ)) + Real.log (1 / (ζ : ℝ))) ^ k),
       PnRateLearners true] := by sorry

end Supplement

end ReplParity
