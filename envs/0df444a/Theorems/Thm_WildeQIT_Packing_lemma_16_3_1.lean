-- Prove2me | Theorems.Thm_WildeQIT_Packing_lemma_16_3_1
-- name    : WildeQIT.Packing.lemma_16_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:24.477173+00:00
-- url     : https://prove2.me/theorems/5e8fcdd9-68b6-4199-858b-ddcc2102176a
-- title:
--   Packing Lemma: $\mathbb E_{\mathcal C}\{\frac1{|\mathcal M|}\sum_m\mathrm{Tr}\{\Lambda_m\sigma_{C_m}\}\}\ge1-2(\varepsilon+2\sqrt\varepsilon)-4|\mathcal M|d/D$
-- statement:
--   **Lemma 16.3.1 (Packing Lemma).** Let $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ be an ensemble of density operators on a finite-dimensional Hilbert space $\mathcal H$, over a finite alphabet $\mathcal X$, with expected density operator $\sigma=\sum_xp_X(x)\sigma_x$. Let $\Pi$ (the code subspace projector) and $\Pi_x$, $x\in\mathcal X$ (the codeword subspace projectors) be orthogonal projectors on $\mathcal H$ such that, for every $x\in\mathcal X$,
--
--   $$\operatorname{Tr}\{\Pi\sigma_x\}\ge1-\varepsilon,\qquad\operatorname{Tr}\{\Pi_x\sigma_x\}\ge1-\varepsilon,\qquad\operatorname{Tr}\{\Pi_x\}\le d,\qquad\Pi\sigma\Pi\le\frac1D\Pi,$$
--
--   where $\varepsilon\in(0,1)$, $D>0$ and $d\in(0,D)$, and the last condition is the operator (Loewner) order. Let $\mathcal M$ be a finite nonempty message set, and let the codewords $C_m$, $m\in\mathcal M$, be drawn independently, each according to $p_X$. Then for every code there is a POVM $\{\Lambda_m\}_{m\in\mathcal M}$ (which may depend on the code) such that
--
--   $$\mathbb E_{\mathcal C}\Bigl\{\frac1{|\mathcal M|}\sum_{m\in\mathcal M}\operatorname{Tr}\{\Lambda_m\sigma_{C_m}\}\Bigr\}\ge1-2\bigl(\varepsilon+2\sqrt\varepsilon\bigr)-\frac{4|\mathcal M|\,d}{D}.$$
--
--   The packing lemma is the one-shot primitive behind the Holevo–Schumacher–Westmoreland theorem and the entanglement-assisted classical capacity theorem: it turns four conditions on an ensemble and a family of projectors into a decoding measurement for about $D/d$ messages.
--
--   **Formalization Note** The expectation over the random code is the finite sum over all codes $c:\mathcal M\to\mathcal X$ weighted by $p(\mathcal C)=\prod_mp_X(c_m)$ (16.17). The POVM is a function of the code. Projectors are Hermitian idempotents, and $\Pi\sigma\Pi\le\frac1D\Pi$ is positive semi-definiteness of $\frac1D\Pi-\Pi\sigma\Pi$. Traces are real parts of complex traces.
--
--   Differences from the source:
--   - encoding: a set M of size |M| (the bound divides by |M|) → a finite type ι with [Nonempty ι]; reason: for an empty message set the average 1/|M| Σ is undefined in the book (Lean's junk value 0), and no POVM indexed by ∅ sums to I
--   - encoding: E_C over the random code C = {C_m} with C_m i.i.d. ∼ p_X → finite sum Σ_c (∏_m p_X(c_m)) · (…) over all c : ι → X; reason: this is the book's expectation (16.10), (16.17)
--   - encoding: the operator inequality ΠσΠ ≤ (1/D)Π (16.14) → ((1/D)Π − ΠσΠ).PosSemidef; reason: definition of the operator order
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 16.3.1, eqs. (16.11)–(16.15), pp. 488–489 (ensemble: Definition 16.2.1, p. 487)

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_Packing_expectedState
import Definitions.Def_WildeQIT_Packing_IsPOVM
import Definitions.Def_WildeQIT_Packing_codeProb
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §16.3, Lemma 16.3.1
(Packing Lemma), eqs. (16.11)–(16.15), pp. 488–489.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Lemma 16.3.1 (Packing Lemma)** (Wilde, arXiv:1106.1445v8, pp. 488–489). Let
`{p_X(x), σ_x}_{x ∈ 𝒳}` be an ensemble of density operators on `H` with expected density operator
`σ = ∑_x p_X(x) σ_x` (Definition 16.2.1). Let `Π` and `{Π_x}_{x ∈ 𝒳}` be projectors on `H` with
`Tr{Π σ_x} ≥ 1 − ε` (16.11), `Tr{Π_x σ_x} ≥ 1 − ε` (16.12), `Tr{Π_x} ≤ d` (16.13) and
`Π σ Π ≤ (1/D) Π` (16.14), where `ε ∈ (0, 1)`, `D > 0` and `d ∈ (0, D)`. Let `ℳ` be a finite message
set and let the codewords `C_m`, `m ∈ ℳ`, be drawn independently according to `p_X`. Then there is,
for every code, a POVM `{Λ_m}_{m ∈ ℳ}` such that
`E_C{(1/|ℳ|) ∑_{m ∈ ℳ} Tr{Λ_m σ_{C_m}}} ≥ 1 − 2(ε + 2√ε) − 4 |ℳ| d / D` (16.15).

**Formalization Note.** Finite-dimensional Hilbert space (basis indexed by `n`), finite alphabet
`X` and finite, nonempty message set `ι` (the book divides by `|ℳ|`). `P` stands for the book's `Π`
and `Px x` for `Π_x` (`Π` is reserved Lean syntax); a projector is a Hermitian idempotent
(`IsStarProjection`). The operator inequality (16.14) is positive semi-definiteness of
`(1/D) Π − Π σ Π`. The POVM may depend on the code: `Λ c` is a POVM for every code `c : ι → X`,
and the expectation over the random code is the finite sum weighted by
`codeProb p c = ∏_m p_X(c_m)` (16.17). Traces are real parts of complex traces. -/
theorem lemma_16_3_1 {X n ι : Type} [Fintype X] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Nonempty ι] (p : FinDist X) (σ : X → Matrix n n ℂ) (hσ : ∀ x, IsDensityOperator (σ x)) (P : Matrix n n ℂ) (Px : X → Matrix n n ℂ) (hP : IsStarProjection P) (hPx : ∀ x, IsStarProjection (Px x)) (ε D d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD : 0 < D) (hd0 : 0 < d) (hdD : d < D) (h11 : ∀ x, 1 - ε ≤ (P * σ x).trace.re) (h12 : ∀ x, 1 - ε ≤ (Px x * σ x).trace.re) (h13 : ∀ x, (Px x).trace.re ≤ d) (h14 : (((1 / D : ℝ) : ℂ) • P - P * expectedState p σ * P).PosSemidef) : ∃ Λ : (ι → X) → ι → Matrix n n ℂ, (∀ c, IsPOVM (Λ c)) ∧ 1 - 2 * (ε + 2 * Real.sqrt ε) - 4 * (Fintype.card ι : ℝ) * d / D ≤ ∑ c : ι → X, codeProb p c * ((Fintype.card ι : ℝ)⁻¹ * ∑ m, (Λ c m * σ (c m)).trace.re) := by sorry

end WildeQIT.Packing
