-- Prove2me | Theorems.Thm_PolyTimeMBLG_Monotone_theorem_11
-- name    : PolyTimeMBLG.Monotone.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:10.910263+00:00
-- url     : https://prove2.me/theorems/aa12c5b6-0ab2-4692-9973-e744eea5ca23
-- title:
--   Theorem 11 — monotone functions with at most p(n) maxterms are polynomial-time MBLG with (n+1)p(n) mistakes
-- statement:
--   Let $p$ be any polynomial and, for $n\ge1$, let $F_n$ be the family of languages $f^{-1}(1)\subseteq\{0,1\}^n$ of all monotone Boolean functions $f:\{0,1\}^n\to\{0,1\}$ with at most $p(n)$ maxterms (maximal elements of $f^{-1}(0)$ in the coordinatewise order). Then $\{F_n\}_{n\ge1}$ is polynomial-time MBLG, with the explicit mistake bound $(n+1)\,p(n)$:
--
--   1. there is a polynomial $q$ with $|F_n|\le 2^{q(n)}$ for every $n\ge1$;
--   2. there is a single generator $G$, computed by one Turing machine within a polynomial number of steps in the length of the encoded input $(1^n,x^1\cdots x^i)$, such that for every $n\ge1$, every $L\in F_n$ and every enumeration $x^1,\dots,x^{|L|}$ of $L$,
--   $$\#\Bigl\{\,i\in\{0,\dots,|L|-1\}\ :\ G(1^n,x^1\cdots x^i)\notin L\setminus\{x^1,\dots,x^i\}\Bigr\}\ \le\ (n+1)\,p(n).$$
--
--   The generator sees only $n$ and the words printed so far; it receives no feedback and no description of $f$. Whenever $F_n$ is nonempty, $p(n)\ge0$, so $(n+1)p(n)\le 2n\,p(n)$ for $n\ge1$; when $F_n$ is empty there is no mistake constraint. Thus the bound is the paper's $O(p(n)\cdot n)$, and in particular a polynomial number of mistakes, so the family is polynomial-time MBLG in the sense of Definition 6 (Theorem 1).
--
--   The result shows that efficient generation is possible for every class of monotone functions with polynomially many maxterms, for instance disjunctions of variables (one maxterm) and monotone functions computed by polynomial-size decision trees (Corollary 2). Corollary 24(b) of the paper shows the order $n\cdot p(n)$ cannot be improved.
--
--   **Formalization Note** The polynomial $p$ has real coefficients and is compared with the number of maxterms cast to $\mathbb R$; this covers every coefficient convention, and where $p(n)<0$ the family is empty. The explicit constant comes from the proof on pp. 7–8: mistakes occur only at crucial moments and only on maxterms of $f$, and by Lemma 12 (at most $2^n$ crucial moments, so a counter value $n+2$ is impossible) each maxterm is output there at most $n+1$ times, giving at most $(n+1)\cdot\#\text{maxterms}\le (n+1)p(n)$ mistakes. Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` on the encoding over `Option Bool` of length $(n+1)(i+1)$ described in the definitions, with the output as the list of $n$ bits; the machine is required on every history, including those with $n=0$.
--
--   Differences from the source:
--   - generalization: at most $O(p(n)\cdot n)$ mistakes → at most $(n+1)\,p(n)$ mistakes for every $n\ge1$; reason: the explicit bound is what the proof on pp. 7–8 with Lemma 12 yields, and, wherever $F_n$ is nonempty, $p(n)\ge0$ and $(n+1)p(n)\le 2n\,p(n)$ for $n\ge1$, giving the source's $O(p(n)\cdot n)$ and hence $\mathrm{poly}(n)$ mistakes.
--   - encoding: families are indexed by $n\ge1$, and a generator takes a natural-number length → the generator and machine also handle $n=0$, while size and mistake guarantees range over $n\ge1$; reason: this makes the natural-number input domain explicit without adding a family guarantee at zero; there are only two zero-length histories, with the unique empty word as output.
--   - encoding: "any polynomial $p(n)$" → $p\in\mathbb R[X]$ compared with the maxterm count cast to $\mathbb R$; reason: the source fixes no coefficient ring; real coefficients include every choice, and $p(n)<0$ only empties $F_n$.
--   - encoding: running time $\mathrm{poly}(n(i+1))$ → one Mathlib `FinTM2` machine and one polynomial with natural coefficients evaluated at the encoding length $(n+1)(i+1)$; reason: for $n\ge1$, $n(i+1)\le(n+1)(i+1)\le 2n(i+1)$, so the two notions of polynomial time coincide, and natural-coefficient polynomials majorize every polynomial on $\mathbb N$.
--   - encoding: mistake bound $e:\mathbb N\to\mathbb N$ in Definition 5 → a real-valued bound $e(n)=(n+1)p(n)$; reason: on every tested language $L\in F_n$, the maxterm cap forces $p(n)\ge0$, hence $e(n)\ge0$, and the real bound equals its natural floor bound; if $p(n)<0$, $F_n$ is empty and no bound is tested.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Theorem 11 (Restatement of Theorem 1), p. 7, proof pp. 7–8; Theorem 1, p. 4; model §3, Definitions 5–6, p. 5. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation
import Definitions.Def_PolyTimeMBLG_Monotone_MonotoneFamily

namespace PolyTimeMBLG.Monotone

/-- Theorem 11 (= Theorem 1), p. 7: for every polynomial `p`, the family of monotone Boolean
functions with at most `p(n)` maxterms is polynomial-time MBLG, with one polynomial-time
generator making at most `(n + 1) · p(n)` mistakes for every `n ≥ 1`. -/
theorem theorem_11 (p : Polynomial ℝ) :
    IsPolyTimeMBLGWith (monotoneFamily p) (fun n => ((n : ℝ) + 1) * p.eval (n : ℝ)) := by sorry

end PolyTimeMBLG.Monotone
