-- Prove2me | Theorems.Thm_WildeQIT_Packing_corollary_16_5_1
-- name    : WildeQIT.Packing.corollary_16_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:23.031441+00:00
-- url     : https://prove2.me/theorems/1a0c7195-8e69-4073-8e3f-8336efb50ba6
-- title:
--   Derandomized packing lemma: a code with $\mathrm{Tr}\{\Lambda_m\sigma_{c_m}\}\ge1-4(\varepsilon+2\sqrt\varepsilon)-16|\mathcal M|d/D$ for all $m$
-- statement:
--   **Corollary 16.5.1.** Let $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ be an ensemble of density operators on a finite-dimensional Hilbert space $\mathcal H$ over a finite alphabet, with expected density operator $\sigma$, and let $\Pi$ and $\{\Pi_x\}_{x\in\mathcal X}$ be orthogonal projectors on $\mathcal H$ with, for every $x$,
--
--   $$\operatorname{Tr}\{\Pi\sigma_x\}\ge1-\varepsilon,\qquad\operatorname{Tr}\{\Pi_x\sigma_x\}\ge1-\varepsilon,\qquad\operatorname{Tr}\{\Pi_x\}\le d,\qquad\Pi\sigma\Pi\le\frac1D\Pi,$$
--
--   where $\varepsilon\in(0,1)$ and $d\in(0,D)$. Let $\mathcal M$ be a finite nonempty message set. Then there exist a code $\mathcal C_0=\{c_m\}_{m\in\mathcal M}$ with codewords $c_m\in\mathcal X$ and a POVM $\{\Lambda_m\}_{m\in\mathcal M}$ such that
--
--   $$\operatorname{Tr}\{\Lambda_m\sigma_{c_m}\}\ge1-4\bigl(\varepsilon+2\sqrt\varepsilon\bigr)-\frac{16|\mathcal M|\,d}{D}\qquad\text{for every }m\in\mathcal M.$$
--
--   This is the derandomized and expurgated form of the packing lemma: a single deterministic code and decoder whose maximal error probability is small, which is what a coding theorem needs.
--
--   **Formalization Note** Same conventions as the packing lemma (Lemma 16.3.1). $D>0$ follows from $0<d<D$. Codewords need not be distinct.
--
--   Differences from the source:
--   - encoding: a set M of size |M| → a finite type ι with [Nonempty ι]; reason: no POVM indexed by ∅ sums to I, and the book's message set is a set of messages to send
--   - encoding: the operator inequality ΠσΠ ≤ (1/D)Π (16.73) → ((1/D)Π − ΠσΠ).PosSemidef; reason: definition of the operator order
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 16.5.1, eqs. (16.70)–(16.74), p. 496

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_Packing_expectedState
import Definitions.Def_WildeQIT_Packing_IsPOVM
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §16.5, Corollary 16.5.1,
eqs. (16.70)–(16.74), p. 496.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Corollary 16.5.1** (Wilde, arXiv:1106.1445v8, p. 496). Under the hypotheses of the packing
lemma, `Tr{Π σ_x} ≥ 1 − ε` (16.70), `Tr{Π_x σ_x} ≥ 1 − ε` (16.71), `Tr{Π_x} ≤ d` (16.72) and
`Π σ Π ≤ (1/D) Π` (16.73) with `ε ∈ (0, 1)` and `d ∈ (0, D)`, for every finite message set `ℳ`
there are a code `C_0 = {c_m}_{m ∈ ℳ}` with codewords in `𝒳` and a POVM `{Λ_m}_{m ∈ ℳ}` with
`Tr{Λ_m σ_{c_m}} ≥ 1 − 4(ε + 2√ε) − 16 |ℳ| d / D` for every `m ∈ ℳ` (16.74).

**Formalization Note.** Same conventions as `WildeQIT.Packing.lemma_16_3_1`: finite-dimensional
Hilbert space, finite alphabet, finite nonempty message set `ι`; `P`, `Px x` for `Π`, `Π_x`
(Hermitian idempotents); (16.73) as positive semi-definiteness of `(1/D) Π − Π σ Π`. `D > 0`
follows from `0 < d < D`. Codewords need not be distinct. -/
theorem corollary_16_5_1 {X n ι : Type} [Fintype X] [Fintype n] [DecidableEq n] [Fintype ι] [Nonempty ι] (p : FinDist X) (σ : X → Matrix n n ℂ) (hσ : ∀ x, IsDensityOperator (σ x)) (P : Matrix n n ℂ) (Px : X → Matrix n n ℂ) (hP : IsStarProjection P) (hPx : ∀ x, IsStarProjection (Px x)) (ε D d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd0 : 0 < d) (hdD : d < D) (h70 : ∀ x, 1 - ε ≤ (P * σ x).trace.re) (h71 : ∀ x, 1 - ε ≤ (Px x * σ x).trace.re) (h72 : ∀ x, (Px x).trace.re ≤ d) (h73 : (((1 / D : ℝ) : ℂ) • P - P * expectedState p σ * P).PosSemidef) : ∃ c : ι → X, ∃ Λ : ι → Matrix n n ℂ, IsPOVM Λ ∧ ∀ m, 1 - 4 * (ε + 2 * Real.sqrt ε) - 16 * (Fintype.card ι : ℝ) * d / D ≤ (Λ m * σ (c m)).trace.re := by sorry

end WildeQIT.Packing
