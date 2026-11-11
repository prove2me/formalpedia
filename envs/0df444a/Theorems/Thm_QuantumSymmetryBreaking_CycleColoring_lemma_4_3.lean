-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_lemma_4_3
-- name    : QuantumSymmetryBreaking.CycleColoring.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:47.311036+00:00
-- url     : https://prove2.me/theorems/0d2faff1-9c09-4df9-b5a3-baa11f4c76b1
-- title:
--   Lemma 4.3 — $V_n\in\mathcal S$ and $\|E-S(V_n)\|_F\le\lambda^n$
-- statement:
--   Let $s\ge10^4$ and let $V_0=0$, $V_{n+1}=V_n+\frac2s(E-S(V_n))$ be the iterates of eq. (2), with $E=|e\rangle\langle e|$. There is a real $\lambda<1$ such that for every $n\ge1$:
--
--   1. (V1) $V_n\in\mathcal S=\operatorname{span}\{|g\rangle\langle h|:g,h\in G\}$, i.e. $V_n$ has finitely many nonzero coefficients;
--   2. (V2) $$\|E-S(V_n)\|_F\le\lambda^n .$$
--
--   So the $V_n$ are finite combinations of matrix units and approximately solve $S(V)=E$, the property (T2) needed for the 1-dependent colouring.
--
--   Differences from the source:
--   - reading: “$\|\cdots\|\le\lambda^n$ for some $\lambda<1$” for every $n\ge1$ → one $\lambda<1$ chosen before $n$, the bound holding for every $n\ge1$; reason: $\lambda$ is the constant $3/4+24/\sqrt{2s}$ of Lemma 4.5 (proof of Lemma 4.3, p.14); a $\lambda$ depending on $n$ would make the bound vacuous
--   - encoding: operators $X$ on $\ell^2(G)$, and $X\in\mathcal S=\operatorname{span}\{|g\rangle\langle h|\}$ → coefficient arrays $X(g,h)=\langle g|X|h\rangle$; $X\in\mathcal S$ means finitely many nonzero coefficients; $L_i,R_i$ act by reindexing; reason: $L_i,R_i$ permute the basis, so every operator in the statement is determined by its coefficients and all products used are reindexings
--   - encoding: $\|\cdot\|_F$ and $\|\cdot\|_w$ of operators as nonnegative reals → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the norms are defined for every coefficient array, so no default value replaces a divergent sum; on $\mathcal S$ they are the finite real values of the source
--   - encoding: generators indexed by $[s]=\{1,\dots,s\}$ → generators indexed by `Fin s` = $\{0,\dots,s-1\}$; reason: relabelling only
--   - encoding: $G=\langle g_1,\dots,g_s\mid g_i^2=e\rangle$ with word length $|g|$ → the universal Coxeter group on `Fin s` (Coxeter matrix with off-diagonal entries 0, Mathlib's encoding of $\infty$) with its Coxeter length; reason: the same presentation; Coxeter length is the reduced-word length
-- source:
--   Flin, Li, Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), source.pdf SHA-256 121c1ecfd6ed3365b5424f6f5978549d12510d800fb87cb8d2f5e110600a542e, Lemma 4.3, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_InfiniteConstruction

open scoped ENNReal

namespace QuantumSymmetryBreaking.CycleColoring

/-- Lemma 4.3, Flin, Li, Suomela, *Quantum Advantage for Distributed Symmetry Breaking*, STOC 2027 submission #863 (October 2026), p.14 (PDF p.17).
For `s ≥ 10^4` there is `λ < 1` (fixed before `n`) such that for every `n ≥ 1`:
(V1) `V_n ∈ S = span{|g⟩⟨h|}`, and (V2) `‖E − S(V_n)‖_F ≤ λ^n`. -/
theorem lemma_4_3 (s : ℕ) (hs : 10 ^ 4 ≤ s) :
    ∃ c : ℝ, c < 1 ∧ ∀ n : ℕ, 1 ≤ n →
      InSpan (opV s n) ∧ opFrob (opE s - opS (opV s n)) ≤ ENNReal.ofReal (c ^ n) := by sorry

end QuantumSymmetryBreaking.CycleColoring
