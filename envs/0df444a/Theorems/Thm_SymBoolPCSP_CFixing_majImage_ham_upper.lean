-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_majImage_ham_upper
-- name    : SymBoolPCSP.CFixing.majImage_ham_upper
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:08:57.963085+00:00
-- url     : https://prove2.me/theorems/1a50b454-778a-49f2-935e-d36458195d37
-- title:
--   Upper half of Maj(Ham_k(S)): weights ≤ 2·max S − 1, and every weight in [ℓ, 2·max S − 1] occurs
-- statement:
--   Let $k \ge 0$ and $S \subseteq \mathbb Z_{\ge 0}$, and let $w \in S$ be its maximum ($s \le w$ for all $s \in S$), with $w \le k$. Suppose some $\ell \in S$ has $\ell \ge 1$. Write $\mathrm{Maj}(P) = \bigcup_{L\text{ odd}} \mathrm{Maj}_L(P)$. Then:
--
--   1. every $y \in \mathrm{Maj}(\mathrm{Ham}_k(S))$ has Hamming weight $|y| \le 2w - 1$;
--   2. for every $b$ with $\ell \le b \le k$ and $b \le 2w - 1$, we have $\mathrm{Ham}_k(\{b\}) \subseteq \mathrm{Maj}(\mathrm{Ham}_k(S))$.
--
--   This is the "upper half" of Claim 4.8 of Brakensiek–Guruswami; the lower half follows by negation, replacing $S$ by $k - S$.
--
--   Part 1 is double counting: each $1$-column of the output has more than $L/2$ ones, while the total number of ones is at most $Lw$.
--
--   Part 2 is the paper's cyclic-shift construction, with all rows supported as follows:
--
--   - if $b \ge w$: $L = 2b+1$ rows of weight $w$ that are cyclic shifts inside the first $b$ coordinates;
--   - if $b < w$: $L = 4b-1$ rows, namely $2b-1$ copies of the weight-$w$ prefix and $2b$ cyclic shifts of a weight-$\ell$ set inside the first $b$ coordinates.
--
--   In both cases the output is the weight-$b$ prefix. Symmetry of $\mathrm{Ham}_k(S)$ then moves it to an arbitrary $y$ of weight $b$.
--
--   **Formalization Note** $\mathrm{Maj}_L(x)=1$ iff $L < 2|x|$ (`Maj L`), and $\mathrm{Maj}(P)$ is `MajImage P`. The bound $2w-1$ uses natural-number subtraction, which is exact since $w \ge \ell \ge 1$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.2, Claim 4.8 and its proof, p. 19

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Upper half of `Maj(Ham_k(S))`: if `w = max S ≤ k` and `ℓ ∈ S` with `ℓ ≥ 1`, then every tuple in `Maj(Ham_k(S))` has weight at most `2w - 1`, and every weight `b` with `ℓ ≤ b ≤ min(k, 2w - 1)` occurs (`Ham_k({b}) ⊆ Maj(Ham_k(S))`). -/
theorem majImage_ham_upper {k : ℕ} {S : Set ℕ} {l w : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hwS : w ∈ S) (hwk : w ≤ k) (hmax : ∀ s ∈ S, s ≤ w) :
    (∀ y ∈ MajImage (Ham k S), hw y ≤ 2 * w - 1) ∧
    (∀ b : ℕ, l ≤ b → b ≤ k → b ≤ 2 * w - 1 → Ham k {b} ⊆ MajImage (Ham k S)) := by sorry

end SymBoolPCSP.CFixing
