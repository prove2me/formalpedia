-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_lemma_7_3
-- name    : STOC2027BoolCSP.Approximation.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:59.435364+00:00
-- url     : https://prove2.me/theorems/0cb14d3b-0591-4c36-99b1-d4201e1bc41c
-- title:
--   Lemma 7.3 — midpoint quantile sampling, equation (36)
-- statement:
--   For every integer $b\ge2$ there is a sampler that uses exactly $b$ independent unbiased bits and polynomially many bit operations in $b$, and outputs a rational $\tilde Z_b$. Its law admits a coupling with $Z\sim N(0,1)$ satisfying
--   $$\mathbb E\,|Z-\tilde Z_b|\;\le\;20\sqrt b\,2^{-b}.$$
--   Different calls can use independent copies of this coupling. One fixed machine, taking $b$ in unary, is the sampler for every $b$.
--
--   The coupling is an analysis device only: the machine never samples an exact normal. With $N$ independent calls it controls the error of the computed scores $\tilde S=\tilde A\tilde Z$ in equation (37).
--
--   Differences from the source:
--
--   - encoding: a sampler using exactly b unbiased bits and polynomially many bit operations in b → a fixed CoinMachine on input b in unary and a random tape of exactly b bits, halting within P(b) steps with the reduced code of a rational; reason: ordinary finite-bit randomized computation; unary b makes the time bound polynomial in b
--   - encoding: a coupling of Z̃_b with Z ∼ N(0,1); independent copies for different calls → a probability measure π on ℝ × ℝ with marginals N(0,1) and the seed law, |x − y| integrable with mean ≤ 20√b 2^{-b}; for every N the product of N copies of π has marginals the product laws and the same per-coordinate bound; reason: this is the definition of a coupling and of independent copies
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 15 (PDF 18), Lemma 7.3, equation (36)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine

open MeasureTheory ProbabilityTheory

namespace STOC2027BoolCSP.Approximation

/-- Lemma 7.3 (midpoint quantile sampling), equation (36), printed p. 15: one fixed machine, on
input `b ≥ 2` (in unary) and a random tape of exactly `b` unbiased bits, halts within a fixed
polynomial in `b` steps with a rational `Z̃_b`; the law of `Z̃_b` admits a coupling with
`Z ∼ N(0,1)` with `E|Z − Z̃_b| ≤ 20 √b 2^{-b}`, and independent calls admit the product of
independent copies of this coupling. -/
theorem lemma_7_3 :
    ∃ (Mach : CoinMachine) (P : Polynomial ℕ), ∀ b : ℕ, 2 ≤ b →
      ∃ out : (Fin b → Bool) → ℚ,
        (∀ s : Fin b → Bool,
          Mach.HaltsWithin (unaryCode b) (List.ofFn s) (P.eval b) (ratCode (out s))) ∧
        ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
          π.map Prod.fst = gaussianReal 0 1 ∧ π.map Prod.snd = seedLaw b out ∧
          Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π ∧
          ∫ p, |p.1 - p.2| ∂π ≤ 20 * Real.sqrt b * (2 : ℝ) ^ (-(b : ℤ)) ∧
          ∀ N : ℕ,
            (Measure.pi fun _ : Fin N => π).map (fun ω j => (ω j).1) =
                Measure.pi (fun _ : Fin N => gaussianReal 0 1) ∧
            (Measure.pi fun _ : Fin N => π).map (fun ω j => (ω j).2) =
                Measure.pi (fun _ : Fin N => seedLaw b out) ∧
            ∀ j : Fin N, ∫ ω, |(ω j).1 - (ω j).2| ∂(Measure.pi fun _ : Fin N => π) ≤
                20 * Real.sqrt b * (2 : ℝ) ^ (-(b : ℤ)) := by sorry

end STOC2027BoolCSP.Approximation
