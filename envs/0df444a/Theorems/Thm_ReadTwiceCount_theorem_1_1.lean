-- Prove2me | Theorems.Thm_ReadTwiceCount_theorem_1_1
-- name    : ReadTwiceCount.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:55.826206+00:00
-- url     : https://prove2.me/theorems/667f89d9-36db-4362-a2fa-77bebad27fb3
-- title:
--   Theorem 1.1 — a deterministic FPTAS for $Z(F)$ on every read-twice CNF formula
-- statement:
--   **Theorem 1.1.** Let $F$ be an unweighted Boolean CNF formula on an explicitly listed universe of $M$ variables, with at most two total literal occurrences of each variable, and let $N$ be its encoding length, including the variable universe. Given a positive rational $0<\varepsilon\le1$, encoded in binary with length $L_\varepsilon$, a deterministic algorithm outputs a nonnegative rational $\widehat Z$ such that
--   $$(1-\varepsilon)Z(F)\le\widehat Z\le Z(F),\qquad Z(F)=\#\{\sigma:\sigma\models F\}.$$
--   Its bit running time and output length are bounded by a polynomial in $N$, $L_\varepsilon$ and $\varepsilon^{-1}$, with a universal exponent independent of clause width, incidence degree or any structural parameter of $F$.
--
--   Formally: there are one Turing machine $T$ and one constant $c$ such that for every read-twice formula $F$ and every $\varepsilon=p/q$ with $0<p\le q$, $T$ halts on the encoding of $F$ followed by $p$ and $q$ within $c\,(N+L_\varepsilon+\lceil q/p\rceil+2)^c$ steps with a pair $(a,b)$, $b>0$, on its output, where $\widehat Z=a/b$ satisfies the two inequalities and the output has length at most the same bound. No satisfiability, normalization or clause-width assumption is made: unit clauses, empty clauses, repeated literals and free variables are allowed, and an unsatisfiable $F$ forces $\widehat Z=0$.
--
--   The result covers edge covers and sink-free orientations (including degree-two vertices) and their mixtures; at three occurrences no such algorithm exists unless P = NP.
--
--   Differences from the source:
--   - reading: "a deterministic algorithm" with "bit running time" bounded by a polynomial with a universal exponent → one bundled Turing machine `T` (Mathlib's `TM2` with Boolean alphabets) and one constant `c`, chosen before every formula and every $\varepsilon$, via the published `HMBinPacking.OutputsWithin`; reason: the paper fixes no machine and counts bit operations; a `TM2` and a bit-operation algorithm simulate each other with polynomial overhead, and the bound is a polynomial class
--   - encoding: the formula and its encoding length $N$, including the variable universe → `Formula M` (lists of clauses of literals on `Fin M`) with `encodeFormula`: the universe in unary, then the clause count, clause lengths, binary variable indices and sign bits; reason: the paper fixes no format; this explicit encoding includes the universe as the paper requires, and is within a constant factor of any standard one
--   - encoding: $\varepsilon$, a positive rational $\le1$ encoded in binary with length $L_\varepsilon$ → a pair $(p,q)$ with $0<p\le q$ and $\varepsilon=p/q$, input `encodeNat p ++ encodeNat q`, $L_\varepsilon$ its length; reason: a binary encoding of a rational is a numerator–denominator pair; unreduced pairs are included
--   - encoding: the output, a nonnegative rational $\widehat Z$ → a pair $(a,b)$ of naturals with $b>0$, output `encodeNat a ++ encodeNat b`, $\widehat Z=a/b$; reason: every nonnegative rational has this form; the code is injective
--   - encoding: "bounded by a polynomial in $N$, $L_\varepsilon$ and $\varepsilon^{-1}$" with a universal exponent, for time and output length → both bounded by $c\,(N+L_\varepsilon+\lceil q/p\rceil+2)^c$, with $\lceil q/p\rceil=(q+p-1)/p$; reason: $\varepsilon^{-1}\le\lceil q/p\rceil\le2\varepsilon^{-1}$, so a polynomial with a fixed exponent in $N$, $L_\varepsilon$, $\varepsilon^{-1}$ is bounded by such an expression and conversely; the $+2$ keeps the base at least $2$
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Theorem 1.1, display (1), p.1

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ReadTwiceCount_encodeFormula

namespace ReadTwiceCount

open ExponomialAssortment.FPTAS (encodeNat)

/-- **Theorem 1.1** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Theorem 1.1, p.1): for an unweighted
Boolean CNF formula F on an explicitly listed universe of M variables, with at most two total literal
occurrences of each variable, and a positive rational 0 < ε ≤ 1, a deterministic algorithm outputs a
nonnegative rational Ẑ with (1 − ε)Z(F) ≤ Ẑ ≤ Z(F); its bit running time and output length are
bounded by a polynomial in N, L_ε and ε^{−1} with a universal exponent.

**Formalization Note**
- One bundled Turing machine `T` (Mathlib's `TM2` with Boolean alphabets, deterministic) and one
  constant `c` are chosen before every formula and every ε: `c` is the universal exponent.
- The input is the formula's encoding (universe in unary) followed by ε = p/q as the pair
  `encodeNat p ++ encodeNat q` with `0 < p ≤ q`, not necessarily reduced; `L_ε` is the length of
  that pair. The output Ẑ = a/b is the pair `encodeNat a ++ encodeNat b` with `b > 0`.
- The polynomial is written `c·(N + L_ε + ⌈q/p⌉ + 2)^c`, with `⌈q/p⌉ = (q + p − 1)/p ≥ ε^{−1}`.
- No satisfiability, normalization, clause-width or nonempty-clause hypothesis: unit clauses, empty
  clauses, repeated literals and free variables are all allowed (if Z(F) = 0 the output must be 0). -/
theorem theorem_1_1 :
    ∃ (T : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ (M : ℕ) (F : Formula M), ReadTwice F →
      ∀ p q : ℕ, 0 < p → p ≤ q →
        ∃ a b : ℕ, 0 < b ∧ (1 - (p : ℚ) / q) * (Z F : ℚ) ≤ (a : ℚ) / b ∧ (a : ℚ) / b ≤ (Z F : ℚ) ∧
          HMBinPacking.OutputsWithin T (encodeFormula F ++ encodeNat p ++ encodeNat q)
            (encodeNat a ++ encodeNat b)
            (c * (N F + (encodeNat p ++ encodeNat q).length + (q + p - 1) / p + 2) ^ c) ∧
          (encodeNat a ++ encodeNat b).length ≤
            c * (N F + (encodeNat p ++ encodeNat q).length + (q + p - 1) / p + 2) ^ c := by sorry

end ReadTwiceCount
