-- Prove2me | Theorems.Thm_QuadraticRE_theorem_4_12
-- name    : QuadraticRE.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:17:58.212753+00:00
-- url     : https://prove2.me/theorems/e4a5dd93-4bbc-45a9-a7fb-bebc133283f9
-- title:
--   Theorem 4.12 — every mod-2 branching-program function has a degree-two encoding with errors $2^{-\lambda-2}$, $\frac322^{-\lambda-2}$ in time $\mathrm{poly}(\sigma+\lambda)$
-- statement:
--   There are one polynomial $P$ and one encoding construction with the following property. Let $f:\{0,1\}^N\to\{0,1\}^b$ be represented by a list of mod-2 branching programs of total size $\sigma$ (including $N+b$), and let $\lambda\ge1$. Then the construction gives an explicit randomized encoding of $f$ of degree at most two over $\mathbb F_2$, jointly in the input and the random bits, with
--   $$\text{correctness error }\ \delta\le2^{-\lambda-2},\qquad\text{statistical privacy error }\ \varepsilon\le\tfrac32\,2^{-\lambda-2}<2^{-\lambda};$$
--   its random tape, its encoded output, its simulator's coins and its expanded polynomial description have length at most $P(\sigma+\lambda)$; and its construction, encoder, decoder and simulator are computed by fixed polynomial-time machines.
--
--   This is the main result of the paper: statistical randomized encodings of degree two exist for every function, with efficiency polynomial in its branching-program size.
--
--   Differences from the source:
--   - reading: its construction, encoder, decoder and simulator run in time polynomial in σ + λ → one fixed machine of Mathlib's Turing.TM2ComputableInPolyTime, from the bit encoding of the input (all numbers in unary) to the bit encoding of the output, in time polynomial in the input length; reason: Definition 3.7 gives no machine model; the length lemma of the verification file shows the encoded parameters have length between σ+λ and a fixed polynomial in σ+λ (paper.md decision 2)
--   - encoding: an explicit randomized encoding of degree at most two → a monomial description, every monomial of at most two variables, and the encoder its evaluation; reason: Definition 3.2 and the lists of monomials of p.13
--   - encoding: a randomized simulator → a deterministic map on its input and τ uniform coins, with τ at most a fixed polynomial in σ + λ; reason: Definition 3.7: random tapes consist of independent uniform bits and have polynomially bounded length
--   - encoding: 2^{−λ−2}, 2^{−λ} → (1/2)^(λ+2), (1/2)^λ; reason: Lean notation; same numbers
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Theorem 4.12, p.30 (informal form p.1)

import Mathlib
import Definitions.Def_QuadraticRE_IsRE
import Definitions.Def_QuadraticRE_Construction

namespace QuadraticRE

/-- Theorem 4.12 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.30: quadratic encodings of arbitrary functions.

One construction `C` and one polynomial `P`, chosen before the parameters `p = (rep, 1^λ)`. For every
`p`, the description of `C` has degree at most two jointly in the input and tape bits, and is a
`2^{−λ−2}`-correct, `(3/2) 2^{−λ−2}`-private RE of the function represented by `rep`, and all lengths are
at most `P(σ + λ)`. The four algorithms run in polynomial time.

**Formalization Note.** `2^{−k}` is written `(1/2)^k`. Every `rep` is allowed, including `N = 0` and
`b = 0`. The machine time is a polynomial in the length of the encoded input, which is polynomially
related to `σ + λ` by the length lemma of the verification file and the bounds of this theorem. -/
theorem theorem_4_12 :
    ∃ (P : Polynomial ℕ) (C : Construction (Par := Param) (fun p => p.rep.N) (fun p => p.rep.b)),
      (∀ p : Param,
        (C.desc p).DegLE 2 ∧
        IsRE p.rep.eval (C.desc p).eval ((1 / 2 : ℝ) ^ (p.lam + 2)) ((3 / 2) * (1 / 2 : ℝ) ^ (p.lam + 2))
          (C.dec p) (fun y => law (C.sim p y)) ∧
        (3 / 2) * (1 / 2 : ℝ) ^ (p.lam + 2) < (1 / 2 : ℝ) ^ p.lam ∧
        C.ρ p ≤ P.eval (p.rep.size + p.lam) ∧
        C.ℓ p ≤ P.eval (p.rep.size + p.lam) ∧
        C.τ p ≤ P.eval (p.rep.size + p.lam) ∧
        (encDesc (C.desc p)).length ≤ P.eval (p.rep.size + p.lam)) ∧
      C.IsPolyTime encParam := by sorry

end QuadraticRE
