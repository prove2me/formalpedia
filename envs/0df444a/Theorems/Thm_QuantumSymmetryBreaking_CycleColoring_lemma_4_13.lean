-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_4_13
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:10.119435+00:00
-- url     : https://prove2.me/theorems/d27519e7-5610-4939-84fe-a099d98800ab
-- title:
--   Lemma 4.13 — a self-adjoint $W_n$ with $\|V_n'-W_n^2\|_F\le\lambda^n$
-- statement:
--   Let $s\ge10^4$, $n\ge1$, and $\lambda=\frac34+\frac{24}{\sqrt{2s}}$ (the constant of Lemma 4.5; $\lambda<1$ for these $s$). There is a self-adjoint $W_n\in\mathbb C[G\times G]$ such that
--   $$
--   \|V_n'-W_n^2\|_F\le\lambda^n ,
--   $$
--   where $V_n'$ is the vectorization of the iterate $V_n$ of eq. (2). This approximate square root is what makes the operators $K_{\pm i}W_n^2K_{\pm i}$ of §5 positive.
--
--   Differences from the source:
--   - reading: $\lambda$ (not quantified in the statement) → $\lambda=3/4+24/\sqrt{2s}$; reason: the statement's $\lambda$ is the one defined in Lemma 4.5, and the proof bounds the error by exactly this $\lambda^n$
--   - encoding: $Z'$ defined for $Z\in\mathcal S$ → `vec Z` is the source's $Z'$ when $Z$ has finitely many nonzero coefficients, and $0$ otherwise; reason: every argument of `vec` in the statement lies in $\mathcal S$ ($V_n\in\mathcal S$ by Lemma 4.3 (V1), and $P_{\pm i}V_nP_{\mp i}$ has finitely many coefficients), so the placeholder is never used
--   - encoding: operators $X$ on $\ell^2(G)$, and $X\in\mathcal S=\operatorname{span}\{|g\rangle\langle h|\}$ → coefficient arrays $X(g,h)=\langle g|X|h\rangle$; $X\in\mathcal S$ means finitely many nonzero coefficients; $L_i,R_i$ act by reindexing; reason: $L_i,R_i$ permute the basis, so every operator in the statement is determined by its coefficients and all products used are reindexings
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 4.13, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_GroupAlgebra

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 4.13, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.20 (PDF p.23).
For `s ≥ 10^4` and `n ≥ 1` there is a self-adjoint `W_n ∈ ℂ[G × G]` with `‖V_n′ − W_n^2‖_F ≤ λ^n`,
where `λ = 3/4 + 24/√(2s)` is the constant of Lemma 4.5. -/
theorem lemma_4_13 (s : ℕ) (hs : 10 ^ 4 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ∃ W : Alg s, IsSelfAdj W ∧ algFrob (vec (opV s n) - W ^ 2) ≤ lam s ^ n := by sorry

end QuantumSymmetryBreaking.CycleColoring
