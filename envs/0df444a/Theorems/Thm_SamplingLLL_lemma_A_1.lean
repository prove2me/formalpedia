-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_1
-- name    : SamplingLLL.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:52:36.796956+00:00
-- url     : https://prove2.me/theorems/a1b7a080-a2b4-4fce-ad4c-7071ce3ce7c6
-- title:
--   Lemma A.1, p.19 — occupation sampler
-- statement:
--   Let $\nu,\mu$ be probability measures on a finite space $\Omega$, and let $P,S$ be nonnegative kernels with $(P+S)\mathbf 1=\mathbf 1$, for continuation and for termination with an output. Suppose a finite measure $q$ satisfies
--   $$
--   q=\nu+qP,\qquad qS=\mu.
--   $$
--   Then the procedure started from $\nu$ terminates almost surely with law $\mu$, and its occupation measure $\sum_j\nu P^j$ is at most $q$. If every pass stops with probability at least $\delta>0$, its occupation measure equals $q$.
--
--   This is the argument behind the reverse packet circuit, where the input to each pass does not have the source law.
--
--   Differences from the source:
--   - encoding: "terminates almost surely", "occupation measure" → the mass of $\nu P^t$ tends to $0$; the terminal measure and occupation measure are the series $\sum_j\nu P^jS$, $\sum_j\nu P^j$; reason: on a finite space these are the path quantities of the chain
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.1, p.19

import Mathlib

set_option autoImplicit false

open Filter Topology Matrix

namespace SamplingLLL

/-- Lemma A.1 (Occupation sampler), p.19.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.1, p.19.

**Formalization Note.** The chain is on a finite space, so `ν P^j` is its generation-`j` occupation:
termination is the mass of `ν P^t` tending to `0`, the terminal measure is `Σ_j ν P^j S`. -/
theorem lemma_A_1 {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ν μ q : Ω → ℝ) (P S : Matrix Ω Ω ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hP : ∀ x y, 0 ≤ P x y) (hS : ∀ x y, 0 ≤ S x y) (hPS : ∀ x, ∑ y, (P x y + S x y) = 1)
    (hq : ∀ x, 0 ≤ q x) (hfix : q = ν + q ᵥ* P) (hout : q ᵥ* S = μ) :
    Tendsto (fun t : ℕ => ∑ x, (ν ᵥ* P ^ t) x) atTop (𝓝 0) ∧
    (∀ y, HasSum (fun j : ℕ => ((ν ᵥ* P ^ j) ᵥ* S) y) (μ y)) ∧
    (∀ x, Summable (fun j : ℕ => (ν ᵥ* P ^ j) x) ∧ ∑' j : ℕ, (ν ᵥ* P ^ j) x ≤ q x) ∧
    (∀ δ : ℝ, 0 < δ → (∀ x, δ ≤ ∑ y, S x y) → ∀ x, ∑' j : ℕ, (ν ᵥ* P ^ j) x = q x) := by sorry

end SamplingLLL
