-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_proposition_3_2
-- name    : PolyEvalDS.LargeChar.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:58.148845+00:00
-- url     : https://prove2.me/theorems/df6ca6d1-2165-4c3c-8771-4d2d1efaa0e1
-- title:
--   Proposition 3.2 — curve interpolation: $\{0,\dots,B\}^n$ reduces to $\{0,\dots,B'\}^n$ with $rd+1$ queries
-- statement:
--   Let $p$ be a prime and let $n,d,B,r$ be positive integers with $p>rd\ge2$. Put
--   $$B'=\Bigl\lfloor\exp\bigl(\tfrac1r\ln B+r\ln d+r\ln r\bigr)\Bigr\rfloor.$$
--   Then there is an algebraic polynomial evaluation datastructure for input points in $\{0,\dots,B\}^n\subseteq\mathbb F_p^n$, for $n$-variate polynomials of total degree at most $d$ over any field $F\supseteq\mathbb F_p$, with encoding map
--   $$F[X_1,\dots,X_n]_{\le d}\to F^{\{0,\dots,B'\}^n},\qquad f\mapsto (f(a))_a,$$
--   and query complexity $rd+1$.
--
--   Moreover there is $d_0$ such that for all $d\ge d_0$ and $B\ge d^4$:
--
--   1. if $\ln B\le d$ and $r=\lceil\sqrt{\ln B/\ln d}\rceil$, then $B'\le\exp(3\sqrt{\ln B\ln d})$;
--   2. if $\ln B\ge d$ and $r=\lceil\sqrt{\ln B/\ln\ln B}\rceil$, then $B'\le\exp(3\sqrt{\ln B\ln\ln B})$.
--
--   This is the reduction step that the proof of Theorem 1.1 iterates.
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
--   - reading: "for sufficiently large d" → one d₀ before d and p; reason: the threshold of the proof is absolute
--   - encoding: the special cases sit in the proposition with p > rd ≥ 2 in scope → the two bounds on B′ are stated without p; reason: B′ is defined from B, d and r only, and the bounds are real inequalities in those
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Proposition 3.2, p. 7

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Formula
import Definitions.Def_PolyEvalDS_LargeChar_Encoding
import Definitions.Def_PolyEvalDS_LargeChar_Datastructure
import Definitions.Def_PolyEvalDS_LargeChar_Params
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

universe u

/-- Proposition 3.2, p. 7: curve interpolation, with both special cases. -/
theorem proposition_3_2 :
    IsDatastructureFamily.{u} (ι := Prop32Params)
        (fun P => ⟨P.p, P.n, P.d, P.B, curveBox P.B P.d P.r, P.r⟩)
        (fun P => (P.r : ℝ) * (P.d : ℝ) + 1) ∧
      ∃ d₀ : ℕ, ∀ d B : ℕ, d₀ ≤ d → d ^ 4 ≤ B →
        (Real.log B ≤ (d : ℝ) →
          (curveBox B d ⌈Real.sqrt (Real.log B / Real.log d)⌉₊ : ℝ) ≤
            Real.exp (3 * Real.sqrt (Real.log B * Real.log d))) ∧
        ((d : ℝ) ≤ Real.log B →
          (curveBox B d ⌈Real.sqrt (Real.log B / Real.log (Real.log B))⌉₊ : ℝ) ≤
            Real.exp (3 * Real.sqrt (Real.log B * Real.log (Real.log B)))) := by sorry

end PolyEvalDS.LargeChar
