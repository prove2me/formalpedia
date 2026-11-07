-- Prove2me | Theorems.Thm_SmolenskyAC_lemma_1
-- name    : SmolenskyAC.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:44.414195+00:00
-- url     : https://prove2.me/theorems/36fdefe8-51ac-4c8d-9ecf-1d2d2cca59ea
-- title:
--   Lemma 1 — OR is nearly $F$-easy in characteristic $p\neq0$, with $\lambda=p-1$
-- statement:
--   Let $F$ be a field of characteristic $p\ne 0$. Then $\mathrm{OR}$ is nearly $F$-easy with constant $\lambda=p-1$: for every $n$, all Boolean functions $g_1,\dots,g_m$ on $D^n$ and every $l\ge 0$, there are a set $E\subseteq D^n$ with $|E|\cdot 2^l\le 2^n$ and a polynomial $P$ of total degree at most $(p-1)l$ with
--
--   $$P(g_1(x),\dots,g_m(x))=\mathrm{OR}(g_1(x),\dots,g_m(x))\qquad (x\notin E).$$
--
--   This is the approximation step for unbounded fan-in OR gates: they become low-degree polynomials after discarding a $2^{-l}$ fraction of the cube.
--
--   Differences from the source:
--   - generalization: OR is nearly F-easy (some constant λ) → nearly F-easy with λ = p − 1; reason: the degree bound (p − 1)·l with which the proof opens; it implies the existence of a constant
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: dimension at least 2^n − 2^(n−l) → |E|·2^l ≤ 2^n; reason: no truncated subtraction when l > n; same instances
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Lemma 1, p.79 (pdf 3)

import Mathlib
import Definitions.Def_SmolenskyAC_Easy

namespace SmolenskyAC

/-- **Lemma 1** (Smolensky, STOC 1987, p.79): OR is a nearly `F`-easy operation for any field `F`
of characteristic `p ≠ 0`.

**Formalization Note.** Stated with the constant `λ = p − 1` of the proof ("a polynomial … of
degree at most `(p − 1)·l`"), which implies the existence of a constant. -/
theorem lemma_1 (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : p ≠ 0) :
    IsNearlyFEasy F (p - 1) OR := by sorry

end SmolenskyAC
