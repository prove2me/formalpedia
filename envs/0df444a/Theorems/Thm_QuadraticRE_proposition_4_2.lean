-- Prove2me | Theorems.Thm_QuadraticRE_proposition_4_2
-- name    : QuadraticRE.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:12:47.45892+00:00
-- url     : https://prove2.me/theorems/fc174395-173a-4797-a064-fc33f400356d
-- title:
--   Proposition 4.2 — degree two, tape $2(L-1)+3hL$, output $3hL$, $O(Lh)$ operations, $O(Lh(j+1))$ monomials
-- statement:
--   There are a universal constant $K$ and, for all $j,h$, a monomial description of $E_{j,h}$ such that for every $j\ge0$ and $h\ge3$, with $L=4^j$:
--
--   1. the description evaluates to $E_{j,h}$ and every monomial has at most two variables, so $E_{j,h}$ has total degree at most two jointly in the input bits and the tape bits;
--   2. the tape has length $2(L-1)+3hL$ and the output has length $3hL$;
--   3. the description has at most $K\,Lh(j+1)$ monomials;
--   4. straight-line programs over $\mathbb F_2$ of at most $K\,Lh$ gates compute the encoder and the decoder;
--   5. one polynomial-time machine computes the description from $(1^L,1^h)$.
--
--   This is the complexity input to the instantiation of the parameters.
--
--   Differences from the source:
--   - reading: the encoder and decoder use O(Lh) operations over F₂ → straight-line programs of at most K·L·h gates, one universal K; reason: the page counts field operations and names no machine; an SLP pays for each operation and has no branching, so this is the strong reading (paper.md decision 3)
--   - reading: these expressions can be constructed in time polynomial in L and h → one Turing.TM2ComputableInPolyTime machine from the unary pair (1^L, 1^h) to the bit encoding of the description; reason: Definition 3.7 gives no machine model; the length lemma of the verification file shows the encoded parameters have length between σ+λ and a fixed polynomial in σ+λ (paper.md decision 2)
--   - generalization: the expansion and its construction for h ≥ 3 → an expansion and a machine defined for every (j, h), with the properties required for h ≥ 3; reason: a machine must be total on its input type; at h ≥ 3 it is the page's claim
--   - encoding: E_{j,h} has total degree at most two; its expansion has O(Lh(j+1)) monomials → one monomial description that evaluates to E_{j,h}, has every monomial of at most two variables, and has at most K·L·h·(j+1) monomials; reason: a polynomial of degree ≤ 2 is witnessed by such an expansion; the page counts the monomials of that expansion
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Proposition 4.2, p.18

import Mathlib
import Definitions.Def_QuadraticRE_encE
import Definitions.Def_QuadraticRE_SLP
import Definitions.Def_QuadraticRE_PolyTimeFn

namespace QuadraticRE

/-- Proposition 4.2 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.18: degree and complexity of `E_{j,h}`.

**Formalization Note.** One universal `K` for all `O(·)`. Operations are straight-line-program gates
(Decision 3 of the plan). The family `exp` and the machine are total in `h`, but only `h ≥ 3` is
constrained. Input `(1^L, 1^h)` to the machine, which makes the time polynomial in `L` and `h`. -/
theorem proposition_4_2 :
    ∃ (K : ℕ) (exp : ∀ j h, Desc 4 (rho j h) (outLen j h)),
      (∀ j h, 3 ≤ h →
        Expands (exp j h) ∧
        (exp j h).DegLE 2 ∧
        rho j h = 2 * (4 ^ j - 1) + 3 * h * 4 ^ j ∧
        outLen j h = 3 * h * 4 ^ j ∧
        (exp j h).numMonomials ≤ K * (4 ^ j * h * (j + 1)) ∧
        (∃ P : SLP (Fin 4 ⊕ Fin (rho j h)) (Fin (4 ^ j) × Fin h × Fin 3),
          P.size ≤ K * (4 ^ j * h) ∧
          ∀ (x : Fin 4 → F2) (R : Tape j h) (t : Fin (4 ^ j) × Fin h × Fin 3),
            P.eval (Sum.elim x R) t = encE j h (x 0) (x 1) (x 2) (x 3) R t.1 t.2.1 t.2.2) ∧
        (∃ P : SLP (Fin (4 ^ j) × Fin h × Fin 3) Unit,
          P.size ≤ K * (4 ^ j * h) ∧
          ∀ Q : Encoded j h, P.eval (fun t => Q t.1 t.2.1 t.2.2) () = decE j h Q)) ∧
      PolyTimeFn (fun p : ℕ × ℕ => encNat (4 ^ p.1) ++ encNat p.2)
        (fun p => encDesc (exp p.1 p.2)) := by sorry

end QuadraticRE
