-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_Supplement_theorem_1_2
-- name    : PatternRangeCounting1593.RangeCounting.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:07:38.939762+00:00
-- url     : https://prove2.me/theorems/a485074f-4455-4790-9505-46e406b2d332
-- title:
--   Theorem 1.2 — static mixed-free matrices: O(1) entry access in O_t(r + c) bits
-- statement:
--   For every fixed $t$, every binary $t$-mixed-free $r\times c$ matrix $M$ has an $O_t(r+c)$-bit representation supporting arbitrary entry access in $O(1)$ worst-case time. For $d$-twin-ordered matrices this gives $O_d(r+c)$ bits and $O(1)$ time, for fixed $d$. When $\operatorname{supp}(D)$ (the support of the XOR difference array of Equation (2)) is given explicitly, construction takes $O_t(r+c)$ time and working words. Given instead a collection $\mathcal K$ of pairwise disjoint rectangles covering exactly the one-entries of $M$, construction takes $O_t(r+c+|\mathcal K|)$ time and working words.
--
--   The model is the deterministic word RAM with $w=\Theta(\log N)$-bit words, $N=r+c$. Precisely, there is an absolute step bound $T$ such that:
--
--   1. for every $t\ge1$ and every width constant $K\ge2$ there are fixed programs — an entry query $Q$, a support constructor and a rectangle constructor — and constants $C,A,T_0,n_0$ depending only on $t$ and $K$, such that for every $t$-mixed-free binary $r\times c$ matrix $M$ and every admissible word width $w$:
--      - some bit string of length at most $C(r+c)+C$ is an entry-access representation of $M$ for $Q$: for every $(i,j)\in[r]\times[c]$, $Q$ run on the packed bits with registers $(r,c,|\mathrm{bits}|,i,j)$ returns $M[i,j]$ within $T_0$ steps, and within $T$ steps when $r+c\ge n_0$;
--      - on every explicit list of $\operatorname{supp}(D)$ (each position once, any order), the support constructor halts within $A(r+c)+A$ steps and working words and outputs such a representation;
--      - on every list $\mathcal K$ of rectangles $[a,b]\times[p,q]$ ($1\le a\le b\le r$, $1\le p\le q\le c$) that are pairwise disjoint and whose union is exactly $\{(i,j):M[i,j]=1\}$, the rectangle constructor halts within $A(r+c+|\mathcal K|)+A$ steps and working words and outputs such a representation;
--   2. for every $d\ge0$ and every $K\ge2$ there are a fixed query program and constants $C,T_0,n_0$ depending only on $d$ and $K$ such that every $d$-twin-ordered binary $r\times c$ matrix has, for every admissible $w$, an entry-access representation of at most $C(r+c)+C$ bits with the same bounds $T_0$ and (for $r+c\ge n_0$) $T$.
--
--   The space bound holds even when $M$ has $\Theta(rc)$ one-entries, and neither construction reads the dense $r\times c$ matrix.
--
--   **Formalization Note** "Admissible width" is `WidthOK K (r + c) w`. Mixed-freeness and twin orders are the published `TwinWidthI.GridThm.MixedFree` and `TwinWidthI.GridThm.TwinOrdered` (division contraction sequences of error value at most $d$, from singletons to at most one block per axis). Construction runs are the published `BuildsWith`: step count, peak touched memory address (input and output buffer included) and the packed output.
--
--   Differences from the source:
--   - reading: 'for every fixed t' (t ≥ 1 implicit) → hypothesis 1 ≤ t; reason: no (0,0)-division of a nonempty matrix exists, so every nonempty matrix is vacuously 0-mixed-free and the space bound would fail at t = 0; the space-optimality paragraph writes 'every fixed t ≥ 1'
--   - encoding: O_t(r + c) bits; O_t(r + c) and O_t(r + c + |K|) construction time and working words; O_d(r + c) bits → length ≤ C (r + c) + C; BuildsWith time and words ≤ A (r + c) + A, resp. A (r + c + |K|) + A; constants chosen after t (resp. d) and K, before r, c, M; reason: §1.1 subscript convention (also for t and d)
--   - encoding: O(1) worst-case query time (unsubscripted) → a step bound T quantified before every parameter, valid whenever r + c ≥ n₀, plus a parameter-dependent bound T₀ valid for every input; reason: §3.1: an absolute constant number of word operations on sufficiently large inputs, smaller inputs handled by direct lookup; same shape as the published Theorem 1.1
--   - encoding: deterministic word RAM with w = Θ(log N)-bit words, N = r + c (§3.1) → the published RAM of PatternRangeCounting1593_RangeCounting_Machine with every word width w satisfying WidthOK K (r + c) w, for an arbitrary K ≥ 2 on which the constants may depend; reason: WidthOK is Θ(log N) with explicit constants, the same convention as the published Theorem 1.1
--   - encoding: 'supp(D) given explicitly'; 'a collection K of pairwise disjoint rectangles covering exactly the one-entries' → every duplicate-free list enumerating supp(xorDiff M) (two words per position, registers [r, c, |L|]); every list of rectangles (a, b, p, q) with 1 ≤ a ≤ b ≤ r, 1 ≤ p ≤ q ≤ c, any two entries cell-disjoint, union = one-entries (four words per rectangle, registers [r, c, |K|]); reason: fixes the input formats the source leaves implicit; any order is allowed
--   - encoding: 'the representation' of Theorem 1.2, constructed from either input (Corollary 7.2) → one query program per (t, K) serves the existing representation and the outputs of both constructors; reason: Corollary 7.2 constructs 'the representation of Theorem 1.2'
--   - encoding: d-twin-ordered matrix, fixed d → TwinOrdered M d (published definition), every d : ℕ; reason: checked equal to the paper's d-twin order; d = 0 is included and needs no exclusion
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 1.2, printed p. 2 (PDF p. 3); proof §6.2, printed p. 23 (PDF p. 24); Corollary 7.2, printed p. 25 (PDF p. 26); §3.1, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_TwinWidthI_GridThm_Setting
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
set_option autoImplicit false
open PatternRangeCounting1593.RangeCounting TwinWidthI.GridThm

namespace PatternRangeCounting1593.RangeCounting.Supplement

/-- Theorem 1.2 (Static mixed-free matrices), printed p. 2 (PDF p. 3); proof in §6.2 and
Corollary 7.2. Machine model: the published word RAM with `WidthOK K (r + c) w`. The query step
bound `T` is universal (the paper's unsubscripted `O(1)`); the programs and the constants
`C, A, T₀, n₀` depend only on `t` (resp. `d`) and on `K`.

1. Every binary `t`-mixed-free `r × c` matrix has an entry-access representation of at most
   `C (r + c) + C` bits.
2. Every `d`-twin-ordered matrix has an entry-access representation of at most
   `C (r + c) + C` bits, with the same universal `T`.
3. From every explicit listing of `supp(D)`, the fixed constructor builds such a representation
   (for the same query program) within `A (r + c) + A` steps and working words.
4. From every list `K` of pairwise disjoint rectangles covering exactly the one-entries, the
   fixed constructor builds such a representation within `A (r + c + |K|) + A` steps and
   working words. -/
theorem theorem_1_2 :
    ∃ T : ℕ,
      (∀ t : ℕ, 1 ≤ t → ∀ K : ℕ, 2 ≤ K →
        ∃ (query buildS buildR : Program) (C A T₀ n₀ : ℕ),
          ∀ (r c : ℕ) (M : Matrix (Fin r) (Fin c) Bool), MixedFree M t →
            ∀ w : ℕ, WidthOK K (r + c) w →
              (∃ bits : List Bool, bits.length ≤ C * (r + c) + C ∧
                EntryRep w query T T₀ n₀ M bits) ∧
              (∀ L : List (ℕ × ℕ), ListsCells (supp (xorDiff M)) L →
                ∃ bits : List Bool,
                  BuildsWith w buildS (pointsMem L) [r, c, L.length]
                    ((A * (r + c) + A : ℕ) : ℝ) ((A * (r + c) + A : ℕ) : ℝ) bits [] ∧
                  bits.length ≤ C * (r + c) + C ∧
                  EntryRep w query T T₀ n₀ M bits) ∧
              (∀ Ks : List (ℕ × ℕ × ℕ × ℕ), ExactDisjointCover M Ks →
                ∃ bits : List Bool,
                  BuildsWith w buildR (rectsMem Ks) [r, c, Ks.length]
                    ((A * (r + c + Ks.length) + A : ℕ) : ℝ)
                    ((A * (r + c + Ks.length) + A : ℕ) : ℝ) bits [] ∧
                  bits.length ≤ C * (r + c) + C ∧
                  EntryRep w query T T₀ n₀ M bits)) ∧
      (∀ d K : ℕ, 2 ≤ K →
        ∃ (query : Program) (C T₀ n₀ : ℕ),
          ∀ (r c : ℕ) (M : Matrix (Fin r) (Fin c) Bool), TwinOrdered M d →
            ∀ w : ℕ, WidthOK K (r + c) w →
              ∃ bits : List Bool, bits.length ≤ C * (r + c) + C ∧
                EntryRep w query T T₀ n₀ M bits) := by sorry

end PatternRangeCounting1593.RangeCounting.Supplement
