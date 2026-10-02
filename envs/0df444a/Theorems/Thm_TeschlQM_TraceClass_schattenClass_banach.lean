-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_schattenClass_banach
-- name    : TeschlQM.TraceClass.schattenClass_banach
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:49:43.016138+00:00
-- url     : https://prove2.me/theorems/11dcc9f0-e45f-4846-aab0-b25cbbc10312
-- title:
--   Lemma 6.12 — Schatten classes are Banach spaces; variational formula for ‖K‖_p
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and $1 \le p < \infty$. The Schatten class $\mathcal{J}_p(\mathfrak{H})$ with the norm $\|\cdot\|_p$ is a Banach space: $\mathcal{J}_p(\mathfrak{H})$ is a linear subspace of $\mathfrak{L}(\mathfrak{H})$, $\|\cdot\|_p$ satisfies the triangle inequality, $\|cK\|_p = |c|\,\|K\|_p$ and $\|K\|_p = 0 \Rightarrow K = 0$ on it, and every $\|\cdot\|_p$-Cauchy sequence in $\mathcal{J}_p(\mathfrak{H})$ converges in $\|\cdot\|_p$ to an element of $\mathcal{J}_p(\mathfrak{H})$. Moreover, for every compact $K \in \mathfrak{C}(\mathfrak{H})$ (both sides are $\infty$ exactly when $K \notin \mathcal{J}_p(\mathfrak{H})$),
--   $$\|K\|_p = \sup\Big\{ \Big(\sum_j |\langle \psi_j, K\varphi_j\rangle|^p\Big)^{1/p} \;\Big|\; \{\psi_j\},\ \{\varphi_j\} \text{ orthonormal sets} \Big\},$$
--   the supremum being taken over all pairs of orthonormal sets indexed by a common index set.
--
--   **Formalization Note.** The book leaves the range of $p$ implicit; its proof uses the conjugate exponent $q$ with $1/p + 1/q = 1$, and for $p < 1$ the triangle inequality fails, so $1 \le p$ is a hypothesis. "Banach space" is spelled out as the listed properties rather than as a Lean `NormedAddCommGroup` instance on a subtype. Norms, sums and the supremum live in $[0,\infty]$; the supremum ranges over index types in the universe of $\mathfrak{H}$, which covers all orthonormal sets.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 141, Lemma 6.12

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass

namespace TeschlQM.TraceClass

universe u

open scoped ENNReal InnerProductSpace
open Filter Topology

/-- Teschl, Lemma 6.12, p. 141, for `1 ≤ p < ∞`. The space `𝔍_p(ℌ)` together with `‖·‖_p` is a
Banach space: `𝔍_p(ℌ)` is a complex vector subspace of `𝔏(ℌ)`, `‖·‖_p` is a norm on it (triangle
inequality, absolute homogeneity, definiteness), and every `‖·‖_p`-Cauchy sequence in `𝔍_p(ℌ)`
converges in `‖·‖_p` to an element of `𝔍_p(ℌ)`. Moreover, for every compact `K` (the operators on
which (6.19) defines `‖K‖_p`; both sides are `∞` exactly when `K ∉ 𝔍_p(ℌ)`, which is how the book's
completeness proof uses (6.23)),
`‖K‖_p = sup {(∑_j |⟨ψ_j, Kφ_j⟩|^p)^{1/p} | {ψ_j}, {φ_j} ONS}` (6.23), the sup taken over all pairs
of orthonormal sets indexed by a common index set. -/
theorem schattenClass_banach {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (p : ℝ) (hp : 1 ≤ p) :
    (0 : H →L[ℂ] H) ∈ schattenClass H p ∧
    (∀ K ∈ schattenClass H p, ∀ L ∈ schattenClass H p,
      K + L ∈ schattenClass H p ∧ schattenNorm p (K + L) ≤ schattenNorm p K + schattenNorm p L) ∧
    (∀ (c : ℂ), ∀ K ∈ schattenClass H p,
      c • K ∈ schattenClass H p ∧ schattenNorm p (c • K) = (‖c‖₊ : ℝ≥0∞) * schattenNorm p K) ∧
    (∀ K ∈ schattenClass H p, schattenNorm p K = 0 → K = 0) ∧
    (∀ Kseq : ℕ → H →L[ℂ] H, (∀ n, Kseq n ∈ schattenClass H p) →
      (∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, schattenNorm p (Kseq m - Kseq n) < ε) →
      ∃ K ∈ schattenClass H p, Tendsto (fun n => schattenNorm p (Kseq n - K)) atTop (𝓝 0)) ∧
    (∀ K ∈ TeschlQM.Shared.compactOperators H, schattenNorm p K =
      ⨆ (ι : Type u) (ψ : ι → H) (φ : ι → H) (_ : Orthonormal ℂ ψ ∧ Orthonormal ℂ φ),
        (∑' j, (‖⟪ψ j, K (φ j)⟫_ℂ‖₊ : ℝ≥0∞) ^ p) ^ (1 / p)) := by sorry

end TeschlQM.TraceClass
