-- Prove2me | Theorems.Thm_SubexpPrimes_lemma_A_24_fractional_digits
-- name    : SubexpPrimes.lemma_A_24_fractional_digits
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:28.996608+00:00
-- url     : https://prove2.me/theorems/418a04f0-5a43-4c08-b194-205ec994b163
-- title:
--   Lemma A.24 — fractional-digit conversion
-- statement:
--   Consider a network with $m_0$ edges and $w$ weighted vertices whose table values lie in $2^{-p}\mathbb Z\cap[-1,1]$, all other table values being in $\{0,1\}$. For an integer $r\ge0$ set
--
--   $$
--   J=2(m_0+2w+r+3),\qquad P_0=m_0+J+w+2.
--   $$
--
--   One contraction over $R_{P_0,J+1}$, with every table value replaced by its digit polynomial, has coefficients $h_j$ whose decoded value $\widehat Z=\sum_{j\le J}h_j2^{-j}$ satisfies $|\widehat Z-Z(G)|\le2^{-r}$. Decoding the answer and converting the tables take polynomial time, on machines.
--
--   This reduces real weights to one contraction over a ring of polynomial tables at the same scale.
--
--   Differences from the source:
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - reading: yields a rational Ẑ → Ẑ defined by the formula of the proof, p.92; reason: a bare existence would be trivial, with Ẑ = Z(G); this is the source's own rational
--   - reading: converting the tables and decoding the answer take polynomial time → two machine clauses, one for each, polynomial in P + J and in P + ℓ + L; reason: the same model as the rest of the mission; the precision p is bounded by L, since the description holds it in unary
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Lemma A.24, p.75; proof, p.92

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_digitPoly

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Lemma A.24 (Fractional-digit conversion)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.75.

For a network with `m₀` edges and `w` weighted vertices whose table values lie in
`2^{-p}ℤ ∩ [-1, 1]`, all others in `{0, 1}`, and an integer `r ≥ 0`, set
`J = 2(m₀ + 2w + r + 3)`, `P₀ = m₀ + J + w + 2`. (i) One contraction over `R_{P₀,J+1}`, of the digit
polynomials of the tables, yields the rational `Ẑ = ∑_{j≤J} h_j 2^{-j}` with `|Ẑ - Z(G)| ≤ 2^{-r}`.
(ii) Decoding the answer takes polynomial time. (iii) Converting the tables takes polynomial time.

**Formalization Note.** `Ẑ` is defined by the formula on p.92: "yields a rational" as a bare
existence would be trivial, with `Ẑ = Z(G)`. In (iii) the machine `E′` takes the entry input with `P`
and `ℓ` in front, and the bound is uniform over all `P`, `ℓ`; a table's digits are bounded by the
precision, which the description holds in unary. -/
theorem lemma_A_24_fractional_digits :
    (∀ (D : NetDesc) (T : D.Tables ℚ) (r : ℕ), D.EntriesInRange T →
      let J := 2 * (D.m + 2 * D.W.card + r + 3)
      let P₀ := D.m + J + D.W.card + 2
      |digitDecode J (D.net (digitTable D T P₀)).Z - (D.net T).Z| ≤ (2 : ℚ) ^ (-(r : ℤ))) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℕ),
      ∀ (P J : ℕ) (H : TruncPoly P), ∃ k : ℤ, (k : ℚ) / 2 ^ J = digitDecode J H ∧
        RunsWithin A out
          (Encoding.encodeList id [Encoding.encodeNat P, Encoding.encodeNat J, truncWord (J + 1) H])
          (dyadicWord k J) (polyBound K (P + J)) (polyBound K (P + J))) ∧
    (∀ (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
      ∃ (E' : PrimitiveMachine) (out' : Fin E'.tapeCount) (K : ℕ),
      ∀ (D : NetDesc) (T : D.Tables ℚ) (P ℓ : ℕ), D.EntriesInRange T →
        D.EntryComputes E outE T (polyBound c (D.m + D.encode.length))
          (polyBound c (D.m + D.encode.length)) →
        ∀ (v : Fin D.n) (z : {e : Fin D.m // (D.ends e).1 = v ∨ (D.ends e).2 = v} → Bool),
          RunsWithin E' out'
            (Encoding.encodeList id [Encoding.encodeNat P, Encoding.encodeNat ℓ, D.entryInput v z])
            (truncWord ℓ (digitTable D T P v z))
            (polyBound K (P + ℓ + D.encode.length)) (polyBound K (P + ℓ + D.encode.length))) := by sorry

end SubexpPrimes
