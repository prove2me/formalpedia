-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_proposition_3_1
-- name    : PolyEvalDS.LargeChar.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:09.304777+00:00
-- url     : https://prove2.me/theorems/eb74ab9a-17d0-4da7-998f-5b775e473b42
-- title:
--   Proposition 3.1 — line interpolation: $\{0,\dots,B\}^n$ reduces to $\{0,\dots,\lfloor2\sqrt{dB}\rfloor\}^n$ with $d+1$ queries
-- statement:
--   Let $p$ be a prime and let $n,d,B$ be positive integers with $p>d$. Then there is an algebraic polynomial evaluation datastructure for input points in $\{0,\dots,B\}^n\subseteq\mathbb F_p^n$, for $n$-variate polynomials of total degree at most $d$ over any field $F\supseteq\mathbb F_p$, with encoding map
--   $$F[X_1,\dots,X_n]_{\le d}\to F^{\{0,\dots,\lfloor2\sqrt{dB}\rfloor\}^n},\qquad f\mapsto (f(a))_a,$$
--   and query complexity $d+1$.
--
--   Since $B\mapsto2\sqrt{dB}$ has the fixed point $4d$, this is the step that brings the box of Theorem 1.1 down to about $(4d)^n$ in Theorem 1.2.
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
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Proposition 3.1, p. 7

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Formula
import Definitions.Def_PolyEvalDS_LargeChar_Encoding
import Definitions.Def_PolyEvalDS_LargeChar_Datastructure
import Definitions.Def_PolyEvalDS_LargeChar_Params
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

universe u

/-- Proposition 3.1, p. 7: line interpolation, from `{0,…,B}^n` to `{0,…,⌊2√(dB)⌋}^n` with
`d + 1` queries. -/
theorem proposition_3_1 :
    IsDatastructureFamily.{u} (ι := Prop31Params)
      (fun P => ⟨P.p, P.n, P.d, P.B, ⌊2 * Real.sqrt ((P.d : ℝ) * (P.B : ℝ))⌋₊, 0⟩)
      (fun P => (P.d : ℝ) + 1) := by sorry

end PolyEvalDS.LargeChar
