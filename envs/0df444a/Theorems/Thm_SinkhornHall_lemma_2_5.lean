-- Prove2me | Theorems.Thm_SinkhornHall_lemma_2_5
-- name    : SinkhornHall.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:42.693042+00:00
-- url     : https://prove2.me/theorems/724c41aa-b8b7-4f85-aab1-251c01a9997c
-- title:
--   Lemma 2.5 — unboundedness criterion for an unconstrained geometric program
-- statement:
--   Let $q_k>0$ and $\omega_k\in\mathbb R^d$ for $k=1,\dots,m$ with $m\ge2$, and let $f(\xi)=\log\sum_k q_ke^{\omega_k^\top\xi}$ as in (2.5).
--
--   1. $f$ is unbounded below if and only if there is $\xi\in\mathbb R^d$ with $\omega_k^\top\xi<0$ for every $k$.
--   2. Let $q_{\min}=\min_kq_k>0$. If $f(\xi)\le\log q_{\min}$, then $\omega_k^\top\xi<0$ for every $k$.
--
--   Specialized to the logarithm of the capacity, part (2) is the certificate of Corollary 2.6: a point with small enough value strictly separates the origin from all exponent vectors.
--
--   **Formalization Note** The terms are indexed by a finite type with at least two elements; unboundedness below is $\forall M\,\exists\xi,\ f(\xi)<M$.
--
--   Differences from the source:
--   - encoding: k = 1, 2, …, m ≥ 2 → a finite index type K with Nontrivial K; reason: the same instances up to relabelling
--   - encoding: 'f is unbounded below' → ∀ M, ∃ ξ, f ξ < M; reason: definition of unbounded below
--   - reading: log (base not named) → Real.log (natural logarithm); reason: the paper's log is the natural logarithm throughout; Lemma 2.5 itself holds in any base used consistently in f and log q_min, so no instance changes
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.5, p.7

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Lemma 2.5 (unboundedness criterion for an unconstrained geometric program).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.5, p.7: "(1) f is unbounded below if and only if
there is ξ ∈ ℝᵈ such that ω_kᵀξ < 0 holds for every k. (2) Let q_min := min_k q_k > 0. If
f(ξ) ≤ log q_min, then ω_kᵀξ < 0 holds for every k." Here `f(ξ) = log Σ_k q_k e^{ω_kᵀξ}` with
`q_k > 0` and `ω_k ∈ ℝᵈ` ((2.5), p.7).

Both parts, as a conjunction.

**Formalization Note.** `f` is `gpObjective q ω`. The terms are indexed by a finite type `K` with
at least two elements (`Nontrivial K`, the paper's `m ≥ 2`; part (2) is false for a single term with
`ω = 0`). "Unbounded below" is `∀ M, ∃ ξ, f ξ < M`. `q_min` is the minimum
`Finset.univ.inf' _ q`. -/
theorem lemma_2_5 {K : Type*} [Fintype K] [Nontrivial K] {d : ℕ} (q : K → ℝ)
    (hq : ∀ k, 0 < q k) (ω : K → Fin d → ℝ) :
    ((∀ M : ℝ, ∃ ξ : Fin d → ℝ, gpObjective q ω ξ < M) ↔
        ∃ ξ : Fin d → ℝ, ∀ k, ω k ⬝ᵥ ξ < 0) ∧
      ∀ ξ : Fin d → ℝ,
        gpObjective q ω ξ ≤ Real.log (Finset.univ.inf' Finset.univ_nonempty q) →
          ∀ k, ω k ⬝ᵥ ξ < 0 := by sorry

end SinkhornHall
