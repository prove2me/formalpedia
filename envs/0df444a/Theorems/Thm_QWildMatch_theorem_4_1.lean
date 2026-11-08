-- Prove2me | Theorems.Thm_QWildMatch_theorem_4_1
-- name    : QWildMatch.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:18:52.539285+00:00
-- url     : https://prove2.me/theorems/b8a4e618-2948-489d-b81b-292feda9294b
-- title:
--   Theorem 4.1, first three sentences — the truncated and banded tables decide the fixed-start predicate
-- statement:
--   Let $T\in\Sigma^n$ be arbitrary, let $\mu\ge0$ with positive gap costs, let $k\ge0$ and let $0\le s\le n$. Write $m$ for the pattern length and $\ell=m+r_+$. Then:
--
--   1. the truncated table of §4 accepts if and only if some substring starting at $s$ has $\mathrm{ED}_\mu(P,T[s:e])\le k$;
--   2. the same holds when every cell outside $-r_-\le u-i\le r_+$ is set to $+\infty$;
--   3. the band contains at most $m(r_-+r_++1)+r_++1$ cells;
--   4. the fixed-start predicate depends only on the positions $x$ with $s\le x<\min(n,s+\ell)$, and there are at most $m+r_+$ of them.
--
--   This is the exact classical verifier that each search step of the algorithm runs on reconstructed text. The theorem's last printed sentence, about a clean reversible circuit for integer costs, needs a gate model and is not part of this item.
--
--   Differences from the source:
--   - generalization: Theorem 4.1 says arbitrary nonnegative substitution costs while §3 also fixes $\mu(\star,b)=0$ and $\mu(a,a)=0$ → Lean takes any $\mu\ge0$; reason: this covers both readings of the page.
--   - generalization: $O(m(r_-+r_++1)+r_++1)$ arithmetic cells → the explicit bound $m(r_-+r_++1)+r_++1$ on the band cells; reason: the explicit bound implies the $O$ form.
--   - encoding: query at most $m+r_+$ text characters → the predicate is unchanged by any change of the text outside those positions, and the table's word is that clipped window; reason: this is the query-free content of "reads only these characters", since the table is a classical object.
--   - encoding: a threshold $k$ → the hypothesis $k\ge0$; reason: for $k<0$ no alignment exists and the problem is empty.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Theorem 4.1, first three sentences, p.5

import Mathlib
import Definitions.Def_QWildMatch_dpCell

namespace QWildMatch

/-- Theorem 4.1 (Uniform fixed-start verifier), first three sentences, Zhao et al., STOC 2027
submission (file sha256 9e87a9dd…), p.5: the truncated table decides the fixed-start predicate, so does
the banded table, the band has at most `m(r₋ + r₊ + 1) + r₊ + 1` cells, and the predicate depends on at
most `m + r₊` text characters.

**Formalization Note** The cell count is the exact form of the page's `O(m(r₋ + r₊ + 1) + r₊ + 1)`: row
`i = 0` has at most `r₊ + 1` band cells, every other row at most `r₋ + r₊ + 1`. "Query at most `m + r₊`
text characters" is locality: the predicate is unchanged by any change of the text outside
`[s, min(n, s + ℓ))`, and that set has at most `m + r₊` positions. The theorem's last sentence, on a
reversible circuit for integer costs, needs a gate model and is not part of this item. -/
theorem theorem_4_1 {Sym : Type} [Fintype Sym] [Nonempty Sym] {n : ℕ} (cm : CostModel Sym)
    (P : List (Option Sym)) (T : Fin n → Sym) (k : ℝ) (hk : 0 ≤ k) (s : ℕ) (hs : s ≤ n) :
    (dpAccept cm P T k s ↔ FixedStart cm P T k s) ∧
    (bandAccept cm P T k s ↔ FixedStart cm P T k s) ∧
    ((Finset.range (P.length + 1) ×ˢ Finset.range (min (ell cm P k) (n - s) + 1)).filter
        (fun c => inBand cm k c.1 c.2)).card ≤
      P.length * (rMinus cm k + rPlus cm k + 1) + rPlus cm k + 1 ∧
    (∀ T' : Fin n → Sym, (∀ x : Fin n, s ≤ (x : ℕ) → (x : ℕ) < s + ell cm P k → T' x = T x) →
      (FixedStart cm P T' k s ↔ FixedStart cm P T k s)) ∧
    (Finset.univ.filter (fun x : Fin n => s ≤ (x : ℕ) ∧ (x : ℕ) < s + ell cm P k)).card ≤
      P.length + rPlus cm k := by sorry

end QWildMatch
