-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_theorem_1_1
-- name    : PolyEvalDS.LargeChar.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:06.18808+00:00
-- url     : https://prove2.me/theorems/c11ea71c-81bd-4d63-bea4-1d975b879bf5
-- title:
--   Theorem 1.1 — evaluations on $\{0,\dots,d^{60}\}^n$ with $O(d)^{\log_2\ln\ln p+O(1)}\ln p$ queries
-- statement:
--   There are absolute constants $c_1>0$, $c_2$ and $d_0$ such that the following holds for every prime $p>2$, all positive integers $n$ and all $d\ge d_0$. There is an algebraic polynomial evaluation datastructure for input points in $\mathbb F_p^n$, for $n$-variate polynomials of total degree at most $d$ over any field $F\supseteq\mathbb F_p$, with encoding map
--   $$F[X_1,\dots,X_n]_{\le d}\to F^{\{0,\dots,d^{60}\}^n},\qquad f\mapsto (f(a))_a,$$
--   and query complexity at most
--   $$C=(c_1d)^{\log_2\ln\ln p+c_2}\ln p.$$
--
--   Moreover the datastructure size is $d^{O(n)}$: for all $n\ge1$ and $d\ge2$,
--   $$(d^{60}+1)^n\le d^{61n}.$$
--
--   The query bound does not depend on $n$. The theorem is the first half of the goal: the box is still far larger than the one in Theorem 1.2.
--
--   The family predicate $\mathrm{DS}$ used below is defined in the definition item `Datastructure`: one machine, one polynomial time bound and one circuit exponent serve all parameters, and for every input point the machine outputs at most $Q$ cell indices and a division-free formula that recovers $f(a)$ from those cells over every field containing $\mathbb F_p$.
--
--   Differences from the source:
--   - generalization: the circuits ψ and e are arithmetic circuits and may contain constants from F → ψ and e are formulas (trees), and every constant is a natural number, so it lies in F_p ⊆ F; reason: a formula is a circuit and F_p ⊆ F, so the Lean object is an instance of the source object
--   - generalization: the datastructure is stated for one field F ⊇ F_p → one machine and one list of indices and formula e work for all fields F ⊇ F_p, and ψ for all of them too; reason: fixing F gives the source statement
--   - reading: polynomial-time algorithm → at most T(n + |p| + d + |B| + |t| + |aux| + ⌈Q⌉) steps of one multi-stack Turing machine, for a fixed polynomial T, with |·| the bit size and d in unary; reason: the algorithm must print l indices and C is not polynomial in the input size (p. 3), so the bound must include C; polynomial in the input alone would assert the open problem the paper leaves open
--   - encoding: the algorithm is given a ∈ S and its parameters, and outputs indices and a circuit → fixed bit encodings of p, n, d, B, t, aux and a on the input stack, and of the indices and the formula on the output stack, with entries as natural numbers; reason: serialization only; t is a function of the other parameters, and an encoder carries no computed result
--   - reading: a size-s^{O(1)} arithmetic circuit ψ mapping the coefficients to a vector in F^s → one formula per cell with total size at most s^c, s = (t+1)^n, with c one natural number for the whole family; reason: the O(1) is absolute, and a family of formulas of total size s^c is a circuit of size at most s^c
--   - reading: query complexity l → the list of indices has length at most Q; reason: the source uses a bound on l; a shorter list is still a correct query list
--   - reading: for sufficiently large d, with O(·) constants → c₁ > 0, c₂ and d₀ are single reals and a natural number chosen before p, n, d, ε and F; reason: a threshold depending on p would make the theorem trivial; the proofs give absolute constants
--   - encoding: input points a ∈ F_p^n → a is a vector of natural numbers with entries at most p − 1, read in F_p by the cast; reason: every point of F_p^n has this form through ZMod.val
--   - generalization: the datastructure size is d^{O(n)} → (d⁶⁰+1)^n ≤ d^{61n} for all n ≥ 1 and d ≥ 2, the explicit constant 61; reason: it specializes to d^{O(n)}; the box size is exactly (d⁶⁰+1)^n
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Theorem 1.1, p. 8 (first stated p. 3; proof pp. 8-9)

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Formula
import Definitions.Def_PolyEvalDS_LargeChar_Encoding
import Definitions.Def_PolyEvalDS_LargeChar_Datastructure
import Definitions.Def_PolyEvalDS_LargeChar_Params
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

universe u

/-- Theorem 1.1, p. 8: evaluations on `{0,…,d⁶⁰}^n` with query complexity
`O(d)^{log₂ ln ln p + O(1)} ln p`, and datastructure size `d^{O(n)}`, here `d^{61n}`. -/
theorem theorem_1_1 :
    ∃ (c₁ c₂ : ℝ) (d₀ : ℕ), 0 < c₁ ∧
      IsDatastructureFamily.{u} (ι := Thm11Params d₀)
        (fun P => ⟨P.p, P.n, P.d, P.p - 1, P.d ^ 60, 0⟩)
        (fun P => (c₁ * (P.d : ℝ)) ^ (Real.logb 2 (Real.log (Real.log P.p)) + c₂) *
          Real.log P.p) ∧
      ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
        (((d ^ 60 + 1 : ℕ) : ℝ) ^ n) ≤ (d : ℝ) ^ (61 * n) := by sorry

end PolyEvalDS.LargeChar
