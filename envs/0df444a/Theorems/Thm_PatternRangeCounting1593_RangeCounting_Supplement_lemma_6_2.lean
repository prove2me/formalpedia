-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_Supplement_lemma_6_2
-- name    : PatternRangeCounting1593.RangeCounting.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:06:58.134382+00:00
-- url     : https://prove2.me/theorems/2f03d330-47cb-4361-8cec-9afb6708a070
-- title:
--   Lemma 6.2 — counting and construction on a support
-- statement:
--   Fix a permutation pattern $\pi$. Let $P\subseteq[r]\times[c]$ have $m$ distinct cells and suppose its rank permutation $\sigma_P$ avoids $\pi$. Then:
--
--   1. $P$ has a representation of $O_\pi(m+r+c)$ bits answering exact dominance counts $|P\cap([i]\times[j])|$ ($0\le i\le r$, $0\le j\le c$) and exact rectangle counts $|P\cap([i_1,i_2]\times[j_1,j_2])|$ in $O(1)$ time;
--   2. from an explicit list of the cells of $P$ (each exactly once, in any order), a fixed deterministic constructor builds such a representation in $O_\pi(m+r+c)$ time and working words;
--   3. in particular, for fixed $k\ge1$ and a $k$-grid-free $P$, all these bounds hold with $O_k(r+c)$ bits, construction time and working words.
--
--   The model is the deterministic word RAM with $w=\Theta(\log N)$-bit words, $N=r+c$. Precisely: there is an absolute step bound $T$ such that for every $\pi$ and every width constant $K\ge2$ there are fixed programs (constructor, dominance query, rectangle query) and constants $A,C,T_0,n_0$ depending only on $\pi$ and $K$ with the following property. For every $r,c$, every $P$ with $\sigma_P$ avoiding $\pi$ and every word width $w$ admissible for $N$, some bit string of length at most $C(m+r+c)+C$ is a counting representation of $P$ (each query halts with the exact count within $T_0$ steps, and within $T$ steps when $r+c\ge n_0$; a query sees only the packed bits and the registers $r,c,|\mathrm{bits}|$ and its cutoffs); and on every explicit list of $P$ the constructor halts within $A(m+r+c)+A$ steps, touching fewer than $A(m+r+c)+A$ memory words, and outputs such a representation. The third clause is the same statement for every $k\ge1$ with the hypothesis "$P$ is $k$-grid-free" in place of avoidance, the length bound $C(r+c)+C$ and the construction bound $A(r+c)+A$, the programs and constants now depending only on $k$ and $K$.
--
--   The lemma is the bridge between the pattern-avoiding permutation counter and matrix access: it handles cells that share rows and columns and translates matrix cutoffs into the permutation's prefix cutoffs.
--
--   **Formalization Note** "Admissible width" is `WidthOK K (r + c) w`: $2\,b(N)\le w\le K\,b(N)$ for the bit length $b(N)$ of $\max\{2,N\}$. Construction runs are the published `BuildsWith` (step count and peak touched address, including the input and the output buffer).
--
--   Differences from the source:
--   - encoding: O_π(m + r + c)-bit representation; O_π(m + r + c) construction time and working words; O_k(r + c) in the last clause → length ≤ C (m + r + c) + C and BuildsWith time and words ≤ A (m + r + c) + A (resp. C (r + c) + C, A (r + c) + A), with C, A chosen after π (resp. k) and K and before r, c, P; reason: §1.1 subscript convention; the base mission encodes O_π the same way
--   - encoding: O(1) worst-case query time (unsubscripted) → a step bound T quantified before every parameter, valid whenever r + c ≥ n₀, plus a parameter-dependent bound T₀ valid for every input; reason: §3.1: an absolute constant number of word operations on sufficiently large inputs, smaller inputs handled by direct lookup; same shape as the published Theorem 1.1
--   - encoding: deterministic word RAM with w = Θ(log N)-bit words, N = r + c (§3.1) → the published RAM of PatternRangeCounting1593_RangeCounting_Machine with every word width w satisfying WidthOK K (r + c) w, for an arbitrary K ≥ 2 on which the constants may depend; reason: WidthOK is Θ(log N) with explicit constants, the same convention as the published Theorem 1.1
--   - encoding: 'explicit P' → every duplicate-free list enumerating P in 1-based coordinates, stored two words per cell, registers [r, c, m]; reason: fixes the input format the source leaves implicit; any order is allowed
--   - encoding: 'has a representation answering exact dominance and rectangle counts' → a packed bit string read by fixed query programs whose inputs are the registers [r, c, |bits|, cutoffs]; dominance cutoffs 0 ≤ i ≤ r, 0 ≤ j ≤ c; rectangle endpoints in [0, r] and [0, c], an empty interval giving 0; reason: programs fixed per parameter cannot hard-code P; the cutoff ranges are those of the proof's identity |P ∩ ([i] × [j])| = Count(X_i, Y_j)
--   - reading: 'a fixed-k-grid-free support' (k ≥ 1 implicit) → hypothesis 1 ≤ k in the last clause; reason: no (0,0)-division of a nonempty grid exists, so every cell set would be 0-grid-free and the clause would fail at k = 0; ρ_k, used in the proof, is defined for k ≥ 1
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Lemma 6.2, printed p. 22 (PDF p. 23); proof printed pp. 22–23 (PDF pp. 23–24); §3.1, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_TwinWidthI_GridThm_Setting
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Supplement_MatrixAccess
set_option autoImplicit false
open PatternRangeCounting1593.RangeCounting TwinWidthI.GridThm

namespace PatternRangeCounting1593.RangeCounting.Supplement

/-- Lemma 6.2 (Counting and construction on a support), printed p. 22 (PDF p. 23).
Machine model: the published word RAM, word width `w` with `WidthOK K (r + c) w` (`N = r + c`,
`w = Θ(log N)`, `K ≥ 2` arbitrary). The query step bound `T` is universal (the paper's
unsubscripted `O(1)`); programs and the constants `A, C, T₀, n₀` depend only on the fixed
parameter (`π`, resp. `k`) and on `K`.

First part: for a cell set `P ⊆ [r] × [c]` with `m = |P|` cells whose rank permutation avoids
`π`, `P` has a counting representation of at most `C (m + r + c) + C` bits, and from every
explicit listing of `P` the fixed constructor builds such a representation within
`A (m + r + c) + A` steps and working words.
Second part ("in particular"): for `k ≥ 1` and a `k`-grid-free `P`, the same with
`C (r + c) + C` bits and `A (r + c) + A` steps and working words. -/
theorem lemma_6_2 :
    ∃ T : ℕ,
      (∀ (k : ℕ) (π : Equiv.Perm (Fin k)) (K : ℕ), 2 ≤ K →
        ∃ (build domQ rectQ : Program) (A C T₀ n₀ : ℕ),
          ∀ (r c : ℕ) (P : Finset (Fin r × Fin c)), Avoids π (rankPerm P) →
            ∀ w : ℕ, WidthOK K (r + c) w →
              (∃ bits : List Bool, bits.length ≤ C * (P.card + r + c) + C ∧
                CountRep w domQ rectQ T T₀ n₀ P bits) ∧
              ∀ L : List (ℕ × ℕ), ListsCells P L →
                ∃ bits : List Bool,
                  BuildsWith w build (pointsMem L) [r, c, L.length]
                    ((A * (P.card + r + c) + A : ℕ) : ℝ) ((A * (P.card + r + c) + A : ℕ) : ℝ)
                    bits [] ∧
                  bits.length ≤ C * (P.card + r + c) + C ∧
                  CountRep w domQ rectQ T T₀ n₀ P bits) ∧
      (∀ (k : ℕ), 1 ≤ k → ∀ (K : ℕ), 2 ≤ K →
        ∃ (build domQ rectQ : Program) (A C T₀ n₀ : ℕ),
          ∀ (r c : ℕ) (P : Finset (Fin r × Fin c)), ¬ HasGridMinor (indicator P) k →
            ∀ w : ℕ, WidthOK K (r + c) w →
              (∃ bits : List Bool, bits.length ≤ C * (r + c) + C ∧
                CountRep w domQ rectQ T T₀ n₀ P bits) ∧
              ∀ L : List (ℕ × ℕ), ListsCells P L →
                ∃ bits : List Bool,
                  BuildsWith w build (pointsMem L) [r, c, L.length]
                    ((A * (r + c) + A : ℕ) : ℝ) ((A * (r + c) + A : ℕ) : ℝ) bits [] ∧
                  bits.length ≤ C * (r + c) + C ∧
                  CountRep w domQ rectQ T T₀ n₀ P bits) := by sorry

end PatternRangeCounting1593.RangeCounting.Supplement
