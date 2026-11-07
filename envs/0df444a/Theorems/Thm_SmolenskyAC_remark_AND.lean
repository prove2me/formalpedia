-- Prove2me | Theorems.Thm_SmolenskyAC_remark_AND
-- name    : SmolenskyAC.remark_AND
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:42.293307+00:00
-- url     : https://prove2.me/theorems/aac5b344-c34a-4046-8c0c-97e8e1bad587
-- title:
--   Remark after Lemma 1 — AND is nearly $F$-easy in characteristic $p\neq0$, with $\lambda=p-1$
-- statement:
--   Let $F$ be a field of characteristic $p\ne 0$. Then $\mathrm{AND}$ is nearly $F$-easy with constant $\lambda=p-1$: for every $n$, all Boolean $g_1,\dots,g_m$ on $D^n$ and every $l$, there are $E\subseteq D^n$ with $|E|\cdot 2^l\le 2^n$ and a polynomial $P$ of total degree at most $(p-1)l$ with $P(g(x))=\mathrm{AND}(g(x))$ for all $x\notin E$.
--
--   The page derives it from Lemma 1, since AND can be written using OR and NOT.
--
--   Differences from the source:
--   - generalization: the same lemma holds for AND (some constant λ) → nearly F-easy with λ = p − 1; reason: the constant of Lemma 1 carries over through 1 − OR(1 − g); it implies the existence of a constant
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: dimension at least 2^n − 2^(n−l) → |E|·2^l ≤ 2^n; reason: no truncated subtraction when l > n; same instances
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Remark, p.80 (pdf 4)

import Mathlib
import Definitions.Def_SmolenskyAC_Easy

namespace SmolenskyAC

/-- **Remark** after Lemma 1 (Smolensky, STOC 1987, p.80): the same lemma holds for AND, since AND
can be written using OR and NOT. For every field `F` of characteristic `p ≠ 0`, AND is nearly
`F`-easy, with the same constant `λ = p − 1`. -/
theorem remark_AND (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : p ≠ 0) :
    IsNearlyFEasy F (p - 1) AND := by sorry

end SmolenskyAC
