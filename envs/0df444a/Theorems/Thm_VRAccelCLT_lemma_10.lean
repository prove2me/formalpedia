-- Prove2me | Theorems.Thm_VRAccelCLT_lemma_10
-- name    : VRAccelCLT.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:01.585978+00:00
-- url     : https://prove2.me/theorems/17471432-ae9f-41c1-b131-7acab06ddd89
-- title:
--   Lemma 10 (Gelfand's formula): $\rho(P)=\lim_k\|P^k\|^{1/k}$ and $\|P^k\|\le c(\iota)(\rho(P)+\iota)^k$
-- statement:
--   Let $P$ be a real square matrix and $\|\cdot\|$ the matrix 2-norm. Then
--
--   $$
--   \rho(P)=\lim_{k\to\infty}\|P^k\|^{1/k},
--   $$
--
--   and for every $\iota>0$ there is a constant $c=c(\iota)$ such that
--
--   $$
--   \|P^k\|\le c(\iota)\,(\rho(P)+\iota)^k\qquad\text{for all }k\ge1 .
--   $$
--
--   The second clause turns $\rho(P)<1$ into a geometric decay bound on $\|P^k\|$, which Lemma 7 uses to control the remainder terms and the series $\Sigma$.
--
--   **Formalization Note** The 2-norm is Mathlib's operator norm on matrices induced by the Euclidean norm. The limit is taken in $[0,\infty]$, where $\rho(P)$ lives (it is finite). Mathlib's general Banach-algebra form is the reference item `FamousTheorems.gelfand_formula`.
--
--   Differences from the source:
--   - reading: P a square matrix → P a real square matrix; reason: all matrices of the paper are real (P1, P2, H2 and the P of Lemma 7)
--   - generalization: P of size n × n → P indexed by any finite type; reason: specializes to Fin n
--   - encoding: ρ(P) = lim ‖P^k‖^{1/k} in ℝ → the limit of ofReal(‖P^k‖^{1/k}) in [0, ∞]; reason: ρ(P) is finite; same limit
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Lemma 10, p.38

import Mathlib
import Definitions.Def_VRAccelCLT_specRad

open Filter
open scoped Topology Matrix.Norms.L2Operator

namespace VRAccelCLT

/-- **Lemma 10 (Gelfand's formula).** Lei, Shanbhag, arXiv:2006.07769v3, Lemma 10, p.38: "It holds
that ρ(P) = lim_{k→∞} ∥P^k∥^{1/k}, i.e., the spectral radius of P gives the asymptotic growth rate of
∥P^k∥. Then for any ι > 0, there exists a constant c = c(ι) such that ∥P^k∥ ≤ c(ι)(ρ(P) + ι)^k,
∀k ≥ 1."

For every real square matrix `P`, both clauses hold, with `‖·‖` the matrix 2-norm (operator norm
induced by the Euclidean norm).

**Formalization Note.** The norm is Mathlib's `Matrix.Norms.L2Operator` instance (the paper's
"matrix two-norm", Notation, p.5). The limit is taken in `ℝ≥0∞`, where `specRad P` lives; `specRad P`
is finite, so in the second clause `(specRad P).toReal` is `ρ(P)`. The index type is any finite
type. Mathlib's complex Banach-algebra form is `FamousTheorems.gelfand_formula`. -/
theorem lemma_10 {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (‖P ^ k‖ ^ (1 / (k : ℝ)))) atTop (𝓝 (specRad P)) ∧
    ∀ ι : ℝ, 0 < ι → ∃ c : ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖P ^ k‖ ≤ c * ((specRad P).toReal + ι) ^ k := by sorry

end VRAccelCLT
