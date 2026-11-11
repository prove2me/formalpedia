-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_4_11
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:01.713213+00:00
-- url     : https://prove2.me/theorems/34e48ca7-03a7-48bb-830b-069f1a50bfb8
-- title:
--   Lemma 4.11 — $\|X\cdot Y\|_w\le4\|X\|_w\|Y\|_w$ in $\mathbb C[G\times G]$
-- statement:
--   For every $X,Y\in\mathbb C[G\times G]$, with $\|X\|_w=\sum_{k,\ell\ge0}2^{(k+\ell)/2}\|X_{k,\ell}\|_F$ the weighted norm,
--   $$
--   \|X\cdot Y\|_w\le4\|X\|_w\|Y\|_w .
--   $$
--   The product is the group-algebra product $[g,h][g',h']=[gg',hh']$. This Haagerup-type inequality (cf. Haagerup 1979, Lemma 1.3, and Picardello 1986, Lemma 2) makes the weighted norm submultiplicative up to the factor $4$, which the binomial square-root series of Proposition 4.12 needs; the Frobenius norm has no such property.
--
--   Differences from the source:
--   - encoding: $\|\cdot\|_w$ on $\mathbb C[G\times G]$ (used in §4.2 without a separate definition) → the formula of Proposition 4.4 applied to coefficients, summed over the finitely many occurring length pairs; reason: the source identifies $\|Z'\|_w=\|Z\|_w$; blocks with no support contribute $0$
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 4.11, p.19 (PDF p.22); proof Appendix A.2, pp.40–41 (PDF pp.43–44)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_GroupAlgebra

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 4.11, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.19 (PDF p.22); proof in Appendix A.2, pp.40–41.
For every `X, Y ∈ ℂ[G × G]`, `‖X · Y‖_w ≤ 4 ‖X‖_w ‖Y‖_w`. -/
theorem lemma_4_11 (s : ℕ) (X Y : Alg s) : algW (X * Y) ≤ 4 * algW X * algW Y := by sorry

end QuantumSymmetryBreaking.CycleColoring
