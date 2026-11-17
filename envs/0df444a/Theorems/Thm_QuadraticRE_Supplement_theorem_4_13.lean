-- Prove2me | Theorems.Thm_QuadraticRE_Supplement_theorem_4_13
-- name    : QuadraticRE.Supplement.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:55:47.871307+00:00
-- url     : https://prove2.me/theorems/8085f2ac-213c-46b8-8f39-fdd038890286
-- title:
--   Theorem 4.13 — under the easy PRG assumption, polynomial-size circuits have computationally private degree-two encodings with correctness error $2^{-\lambda-2}$ and one input bit per monomial
-- statement:
--   Assume the easy PRG assumption. There is one encoding construction for circuit representations, whose construction, encoder, decoder and simulator are polynomial-time algorithms on the encoding of $(C,1^\lambda)$, with the following properties.
--
--   1. For every Boolean circuit $C$ of fan-in at most two computing $f_C$ and every $\lambda\ge1$, the constructed encoding $E_{C,\lambda}(x;r)$ has total degree at most two jointly in the original input bits $x$ and the independent random bits $r$, every monomial of its expanded polynomial description contains at most one original input bit, and
--   $$\Pr_r\big[\mathrm{Dec}(E_{C,\lambda}(x;r))\neq f_C(x)\big]\le2^{-\lambda-2}\quad\text{for every input }x.$$
--   2. For every family $(C_\lambda)$ of circuits whose size $\sigma(\lambda)$ (including input and output lengths) is polynomial in $\lambda$, the encodings $(E_{C_\lambda,\lambda})$ of the functions $(f_\lambda)$ they compute are computationally private with the constructed simulator.
--
--   This is the circuit-efficient counterpart of Theorem 4.12: the complexity is polynomial in circuit size rather than branching-program size, at the price of a computational assumption and computational privacy.
--
--   Differences from the source:
--   - reading: the encoding, decoder and simulator can be constructed from C_λ in time polynomial in σ(λ) + λ → one construction, chosen before the circuit family, with four fixed machines of Mathlib's Turing.TM2ComputableInPolyTime (construction, encoder, decoder, simulator) on the bit encoding of (C, 1^λ) with all numbers in unary; reason: Definition 3.7 asks for uniform construction and names no machine model; the same convention as the published Theorem 4.12
--   - reading: the easy PRG assumption (a secure PRG computable by mod-2 branching programs constructed in polynomial time) → EasyPRG: stretch ℓ(k) > k for k ≥ 1, representations computed from 1^k in polynomial time, negligible advantage against every nonuniform PPT distinguisher; reason: no stretch is named; minimal stretch is the weakest reading of the hypothesis, so the theorem is the strongest one
--   - encoding: Boolean circuits of fan-in at most two, size = non-input gates + N + b → Circuit with constant gates and arbitrary two-input truth tables in topological order; size = gates + N + b; reason: p.14 fixes no basis; allowing every gate of fan-in ≤ 2 only widens the class of circuits
--   - encoding: a family (C_λ) of size σ(λ) polynomial in λ → Cs : ℕ → Circuit with size(Cs κ) ≤ q(κ) for a polynomial q, index κ used with λ = max κ 1; reason: the index 0 does not affect negligibility
--   - encoding: degree, one-input-per-monomial and correctness for the members of the family → stated for every circuit C and every λ ≥ 1; reason: every pair (C, λ) lies in some polynomial-size family, so the two forms are equivalent
--   - reading: every monomial contains at most one original input bit → at most one input variable per monomial, counted with multiplicity; reason: the multiplicity count implies the count of distinct variables, so this is the stronger reading
--   - encoding: a randomized simulator → a deterministic map on τ uniform coins, τ output by the construction machine; reason: Definition 3.7: random tapes are independent uniform bits of polynomially bounded length
--   - encoding: 2^{−λ−2} → (1/2)^(λ+2); reason: Lean notation; same number
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Theorem 4.13, p.31; easy PRG assumption, p.30; circuit size, p.14

import Mathlib
import Definitions.Def_QuadraticRE_IsRE
import Definitions.Def_QuadraticRE_Supplement_EasyPRG
import Definitions.Def_QuadraticRE_Supplement_CircuitEnc

namespace QuadraticRE.Supplement

open QuadraticRE

/-- Theorem 4.13 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript
(sha256 0c94deae…), p.31: computational quadratic encodings for circuits.

Under the easy PRG assumption there is one construction `K` for circuit representations, whose
construction, encoder, decoder and simulator are polynomial-time machines in the encoding of
`(C, 1^λ)`, such that for every circuit `C` and every `λ ≥ 1` the description `K.desc (C, 1^λ)` has
degree at most two jointly in the input and tape bits, has at most one original input bit in every
monomial, and is a `2^{−λ−2}`-correct encoding of the function `C` computes; and for every family
`(C_λ)` of circuits of size polynomial in `λ`, the resulting family of encodings is computationally
private with the constructed simulator.

**Formalization Note.** `2^{−λ−2}` is `(1/2)^(λ+2)`. The construction is chosen before the circuit
family ("constructed from `C_λ`"). Correctness and the degree and monomial clauses are stated for every
`(C, λ)`; every such pair lies in some polynomial-size family, so this is the page's per-family claim.
Computational privacy is the base mission's `CompPrivate` (Def 3.7). The circuit family is nonuniform. -/
theorem theorem_4_13 (hPRG : EasyPRG) :
    ∃ K : Construction (Par := CParam) (fun p => p.C.N) (fun p => p.C.b),
      K.IsPolyTime encCParam ∧
      (∀ p : CParam,
        (K.desc p).DegLE 2 ∧
        OneInputPerMonomial (K.desc p) ∧
        IsCorrect p.C.eval (K.desc p).eval ((1 / 2 : ℝ) ^ (p.lam + 2)) (K.dec p)) ∧
      ∀ (Cs : ℕ → Circuit) (q : Polynomial ℕ), (∀ κ, (Cs κ).size ≤ q.eval κ) →
        CompPrivate (circuitFamily K Cs) := by sorry

end QuadraticRE.Supplement
