-- Prove2me | Theorems.Thm_SpectralFeedback_lemma_F_3_reverse_pairing
-- name    : SpectralFeedback.lemma_F_3_reverse_pairing
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:48.450691+00:00
-- url     : https://prove2.me/theorems/c1e3c3c6-18ea-4efa-95b6-52d774aaa773
-- title:
--   Lemma F.3 — reverse pairing after balancing: $c\prec2x$
-- statement:
--   Let $s\ge1$, and let $A,B\in\mathbb C^{d\times d}$ be positive semidefinite with $\operatorname{rank}A\le s$ and $\operatorname{rank}B\le s$ and with the same decreasing eigenvalue list $x\in\mathbb R^s_+$ (zero padding allowed): $\lambda_i(A)=\lambda_i(B)=x_i$ for $1\le i\le s$. Let $R=A+B$ and
--
--   $$
--   c_i=\lambda_i(R)+\lambda_{2s+1-i}(R),\qquad 1\le i\le s .
--   $$
--
--   Then
--
--   $$
--   c\ \prec\ 2x .
--   $$
--
--   The vector $c$ need not be decreasing; majorization uses its decreasing rearrangement.
--
--   Together with Schur-concavity this gives the upper bound $\mathcal G^F_{2,s}(R)\le2F(c/2)$ of Theorem H.2.
--
--   **Formalization Note** $R\succeq0$ and the facts that $x$ is decreasing and nonnegative follow from the hypotheses and are not assumed separately. Majorization is the published `RetailVariety.Fashion.Majorized`.
--
--   Differences from the source:
--   - encoding: matrices on $\mathbb C^d$, eigenvalues $\lambda_i$ ($1$-based, padded by zeros) → `Matrix (Fin d) (Fin d) ℂ` for every `d : ℕ`; `eigDesc A (i-1)` (0-based, padded by zeros); reason: Lean indexing convention; same instances
--   - generalization: $R\succeq0$ has dimension at most $2s$, padded by zero coordinates to dimension $2s$ → $R=A+B$ on $\mathbb C^d$ for every $d$; reason: the proof (factor $A=X_1X_1^*$, $B=X_2X_2^*$ with $s$ columns; $K=X^*X$ has the nonzero spectrum of $R$) works for every $d$, since $\operatorname{rank}R\le2s$; for $d\le2s$ padding by zeros changes no $\lambda_i(R)$, so it specializes to the source
--   - encoding: atoms with the same decreasing nonzero eigenvalue list $x\in\mathbb R^s_+$ → `eigDesc A i = x i` and `eigDesc B i = x i` for `i : Fin s`; no separate hypotheses that $x$ is decreasing and nonnegative, or that $R\succeq0$; reason: these follow from the other hypotheses (PSD atoms, sorted eigenvalues), so they exclude nothing
--   - encoding: $c\prec2x$ → `RetailVariety.Fashion.Majorized (pairedVec R s) (2 • x)`; reason: the published majorization sorts both vectors, as the source says
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Lemma F.3, p.93 (PDF p.95)

import Mathlib
import Definitions.Def_SpectralFeedback_pairAtom
import Definitions.Def_RetailVariety_Fashion_Majorization

open scoped ComplexOrder

namespace SpectralFeedback

/-- **Lemma F.3** (Reverse pairing after balancing; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.93 (PDF p.95)). Suppose
`R = A + B`, where both atoms are positive semidefinite, have rank at most `s`, and have the same
decreasing eigenvalue list `x ∈ ℝ^s_+` (zero padding allowed). With `c_i = λ_i(R) + λ_{2s+1−i}(R)`,
`1 ≤ i ≤ s`, one has `c ≺ 2x`.

**Formalization Note** `c` is `pairedVec R s` (0-based). `c ≺ 2x` is the published
`RetailVariety.Fashion.Majorized c (2 • x)`, which uses the decreasing rearrangement of `c`, as the
lemma says. The common eigenvalue list is `x i = λ_{i+1}(A) = λ_{i+1}(B)` for `i < s`; that `x` is
decreasing and nonnegative, and that `R ⪰ 0`, follow from these hypotheses. The source's restriction
"`R` has dimension at most `2s`, padded by zero coordinates to dimension `2s`" is dropped: the
statement is for every dimension `d` (for `d ≤ 2s` it is the source's, since padding by zeros
changes no `λ_i(R)`). -/
theorem lemma_F_3_reverse_pairing (s : ℕ) (hs : 1 ≤ s) {d : ℕ}
    (R A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hRAB : R = A + B) (hrA : A.rank ≤ s) (hrB : B.rank ≤ s)
    (x : Fin s → ℝ) (hxA : ∀ i : Fin s, eigDesc A (i : ℕ) = x i)
    (hxB : ∀ i : Fin s, eigDesc B (i : ℕ) = x i) :
    RetailVariety.Fashion.Majorized (pairedVec R s) ((2 : ℝ) • x) := by sorry

end SpectralFeedback
