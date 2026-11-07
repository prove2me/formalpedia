-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_7
-- name    : SamplingLLL.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:20.306202+00:00
-- url     : https://prove2.me/theorems/6947144b-ef48-46f2-8360-408e2b709e29
-- title:
--   Lemma A.7, p.24 — aggregate response
-- statement:
--   Suppose that, for every pair of task types $i,j$, whenever the input measure $\alpha$ of a type-$i$ row is at most $C\sigma_i$, the aggregate input measure of all direct type-$j$ calls is at most $CM_{ij}\sigma_j$. If $Mh\le\rho h$ for some $h_i\ge1$ and $\rho<1$, then a type-$i$ root makes recursive calls of total expected $h$-weight at most $h_i/(1-\rho)$, and the execution is finite almost surely.
--
--   No independence between calls is assumed: the responses are linear in input measures.
--
--   Differences from the source:
--   - encoding: rows on separate input spaces, "after any earlier calls have been closed by balanced rows" → one finite space for all inputs, and a kernel `Resp i j` for the closed direct-call response; the domination is a hypothesis on it; reason: this is the linearity of kernel application used in the proof, p.24
--   - encoding: "finite almost surely" → the mass of generation $t$ tends to $0$; reason: the total weight being finite is the proof's reason
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.7, p.24

import Mathlib
import Definitions.Def_SamplingLLL_responseGen

set_option autoImplicit false

open Filter Topology

namespace SamplingLLL

/-- Lemma A.7 (Aggregate response), p.24: the domination `α ≤ C σ_i ⇒ (aggregate type-j direct input) ≤
C M_ij σ_j` and `Mh ≤ ρh` give total `h`-weight at most `h_i/(1-ρ)` of the recursive calls from a type-`i`
root, and finiteness almost surely. `Resp i j x y` is the expected direct type-`j` input at `y` of a
type-`i` row started at `x`, after earlier calls have been closed; this response is linear in the input
measure, the fact the paper's proof uses, and no independence between calls is assumed.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.7, p.24.

**Formalization Note.** Types and input spaces are finite; "finite almost surely" is the mass of
generation `t` tending to `0`. -/
theorem lemma_A_7 {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (σ : ι → Ω → ℝ) (hσ : ∀ i x, 0 ≤ σ i x) (hσ1 : ∀ i, ∑ x, σ i x = 1)
    (Resp : ι → ι → Ω → Ω → ℝ) (hResp : ∀ i j x y, 0 ≤ Resp i j x y)
    (M : ι → ι → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (hdom : ∀ (i j : ι) (α : Ω → ℝ) (C : ℝ), 0 ≤ C → (∀ x, 0 ≤ α x) → (∀ x, α x ≤ C * σ i x) →
      ∀ y, ∑ x, α x * Resp i j x y ≤ C * M i j * σ j y)
    (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (ρ : ℝ) (hρ : ρ < 1)
    (hMh : ∀ i, ∑ j, M i j * h j ≤ ρ * h i) (i : ι) :
    Summable (fun t : ℕ => ∑ j, h j * ∑ y, responseGen σ Resp i t j y) ∧
    ∑' t : ℕ, ∑ j, h j * ∑ y, responseGen σ Resp i t j y ≤ h i / (1 - ρ) ∧
    Tendsto (fun t : ℕ => ∑ j, ∑ y, responseGen σ Resp i t j y) atTop (𝓝 0) := by sorry

end SamplingLLL
