-- Prove2me | Theorems.Thm_RSCapacity_ListDecoding_differential_solver
-- name    : RSCapacity.ListDecoding.differential_solver
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:18.984655+00:00
-- url     : https://prove2.me/theorems/8708c6e1-38db-4976-a521-a6dfe4d8d4b3
-- title:
--   Theorem 3.3 — efficient Hasse differential-equation enumeration
-- statement:
--   There is one deterministic finite binary program and positive integers $c,s$, chosen independently of all input data, with the following property. Let $F$ be any finite field of size $q$ and characteristic $p$, let $d\ge0$ and $k\ge1$ be integers, and let $Q(X,Y_0,\ldots,Y_d)$ be any nonzero polynomial, supplied in any sparse presentation with distinct exponents and nonzero coefficients. Assume $p>k$ and $p>\deg_{Y_i}Q$ for every $0\le i\le d$. Write $d_Q$ for its $(1,k,\ldots,k)$ weighted degree. The program outputs precisely all degree-$<k$ solutions, without duplicates, of
--   $$Q(X,f(X),f^{(1)}(X),\ldots,f^{(d)}(X))=0,$$
--   and first halts after at most
--   $$q^{c(d+1)}(1+k+d_Q)^s$$
--   local binary-machine instructions. Here $f^{(j)}$ is the Hasse derivative; field tables, parsing, intermediate work and coefficient output are all charged. This supplies the complete costed enumeration target required by the decoder, without assuming a solver as input.
--
--   Differences from the source:
--   - encoding: q^{O(d)} poly(k,d_Q) → q^{c(d+1)}(1+k+d_Q)^s with universal positive integers c,s; reason: the affine exponent includes d=0 and is linear as d grows; q≥2 absorbs constant prefactors and binary simulation overhead
--   - encoding: an arbitrary finite field and multivariate input Q → all field labellings with full operation tables and all unpadded sparse term lists; actual deterministic tape steps; reason: every finite field and polynomial has this presentation; Yi degrees <p≤q bound sparse input length within the same asymptotic time class; degree and Hasse conventions are unchanged
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), Theorem 3.3, p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Differential

namespace RSCapacity.ListDecoding

/-- Theorem 3.3, submission #495 p.10: a universal linear-in-d exponent
and a fixed polynomial in k,d_Q; actual binary tape instruction count. -/
theorem differential_solver :
    ∃ solver : Program, FuzzyExtractors.ImprovedJSFull.Deterministic solver ∧
      ∃ c s : ℕ, 0 < c ∧ 0 < s ∧
      ∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F)
        (d k : ℕ) (Q : SparsePolynomial F d),
        0 < k → Q.polynomial ≠ 0 → k < ringChar F →
        (∀ i : Fin (d + 1), Q.polynomial.degreeOf i.succ < ringChar F) →
        ExecutesWithin solver (differentialInput P k Q)
          (((Fintype.card F : ℕ) : ℝ) ^ (c * (d + 1)) *
            (1 + (k : ℝ) + differentialDegree k Q.polynomial) ^ s)
          (polynomialOutput P k (differentialTarget k Q.polynomial)) := by sorry

end RSCapacity.ListDecoding
