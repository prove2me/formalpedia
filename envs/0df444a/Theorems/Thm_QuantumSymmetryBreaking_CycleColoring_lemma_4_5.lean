-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_4_5
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:29.105596+00:00
-- url     : https://prove2.me/theorems/3896e69d-fe75-4502-b585-ce64976f669b
-- title:
--   Lemma 4.5 (Contraction Lemma) — $\|X-\tfrac2sS(X)\|_w\le\lambda\|X\|_w$, $\lambda=\tfrac34+\tfrac{24}{\sqrt{2s}}$
-- statement:
--   Let $G$ be the free product of $s\ge1$ copies of $\mathbb Z/2$, let $S(\cdot)$ be the map $S(X)=\sum_{i=1}^s(P_{+i}XP_{-i}+P_{-i}XP_{+i})$ on operators of $\ell^2(G)$, and let $\|\cdot\|_w$ be the weighted norm of Proposition 4.4. For every $X\in\mathcal S=\operatorname{span}\{|g\rangle\langle h|\}$,
--   $$
--   \Bigl\|X-\frac2sS(X)\Bigr\|_w\le\lambda\|X\|_w,\qquad \lambda=\frac34+\frac{24}{\sqrt{2s}} .
--   $$
--   This is the key estimate of §4.1: applied to $R_n=E-S(V_n)$ it shows that each step of the recursion (2) contracts the residual geometrically when $s\ge10^4$ (then $\lambda<1$). The lemma itself holds for every $s$.
--
--   Differences from the source:
--   - encoding: $s$ generators ($[s]$ with $s\ge1$) → hypothesis $1\le s$; reason: at $s=0$ the source's $24/\sqrt{2s}$ and $2/s$ are undefined (Lean would read them as $0$)
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
--   - encoding: operators $X$ on $\ell^2(G)$, and $X\in\mathcal S=\operatorname{span}\{|g\rangle\langle h|\}$ → coefficient arrays $X(g,h)=\langle g|X|h\rangle$; $X\in\mathcal S$ means finitely many nonzero coefficients; $L_i,R_i$ act by reindexing; reason: $L_i,R_i$ permute the basis, so every operator in the statement is determined by its coefficients and all products used are reindexings
--   - encoding: $\|\cdot\|_F$ and $\|\cdot\|_w$ of operators as nonnegative reals → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the norms are defined for every coefficient array, so no default value replaces a divergent sum; on $\mathcal S$ they are the finite real values of the source
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 4.5, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction

open scoped ENNReal

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 4.5 (Contraction Lemma), Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.14 (PDF p.17).
For every `X ∈ S` (finitely many nonzero coefficients), `‖X − (2/s) S(X)‖_w ≤ λ ‖X‖_w` with
`λ = 3/4 + 24/√(2s)`. Stated for every number of generators `s ≥ 1`. -/
theorem lemma_4_5 (s : ℕ) (hs : 1 ≤ s) (X : Op s) (hX : InSpan X) :
    opW (X - ((2 : ℂ) / s) • opS X) ≤ ENNReal.ofReal (lam s) * opW X := by sorry

end QuantumSymmetryBreaking.CycleColoring
