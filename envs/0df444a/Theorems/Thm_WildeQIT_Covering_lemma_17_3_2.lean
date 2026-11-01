-- Prove2me | Theorems.Thm_WildeQIT_Covering_lemma_17_3_2
-- name    : WildeQIT.Covering.lemma_17_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:13.733867+00:00
-- url     : https://prove2.me/theorems/c018aea9-3b3c-4076-b0bb-75fe522550f2
-- title:
--   Operator Markov inequality: $\Pr\{X\not\le A\}\le\mathrm{Tr}\{\mathbb E\{X\}A^{-1}\}$
-- statement:
--   **Lemma 17.3.2 (Operator Markov Inequality).** Let $(\Omega,\mu)$ be a probability space, $\mathcal H$ a finite-dimensional Hilbert space, and $X:\Omega\to\mathcal L(\mathcal H)$ an operator-valued random variable that is positive semi-definite at every outcome, with expectation $\mathbb E\{X\}$. Let $A$ be a fixed positive definite operator on $\mathcal H$. Then
--
--   $$\Pr\{X\not\le A\}\le\operatorname{Tr}\bigl\{\mathbb E\{X\}A^{-1}\bigr\},$$
--
--   where $X\not\le A$ means that $A-X$ is not positive semi-definite.
--
--   This is the first step of the chain operator Markov inequality → Bernstein trick → operator Chernoff bound, which drives the proof of the covering lemma.
--
--   **Formalization Note** $\mathcal H=\mathbb C^n$. The expectation is entrywise and the entries of $X$ are assumed integrable; Lean's integral of a non-integrable function is $0$, while in the book's reading a non-integrable $X$ has an infinite expectation and the bound is trivial. The probability is the measure of the event, as a real number; the trace is the real part of the complex trace.
--
--   Differences from the source:
--   - encoding: a positive semi-definite operator-valued random variable with expectation E{X} → a map $\Omega\to$ matrices, positive semi-definite at every outcome, with integrable entries; reason: integrability only excludes the case where $\mathbb E\{X\}$ is infinite and the bound holds trivially, and Lean's integral would return $0$ there.
--   - encoding: $X\not\le A$ → $A-X$ not positive semi-definite; reason: the book's definition of the operator order (p. 508).
--   - encoding: $\Pr\{X\not\le A\}$ for a measurable random variable → the measure of the set $\{\omega : A-X(\omega)\text{ not PSD}\}$, with no measurability hypothesis beyond the integrable entries; reason: integrable entries make $X$ almost-everywhere measurable, so the event is null-measurable and its measure is the book's probability.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 17.3.2 (Operator Markov Inequality), eq. (17.19), p. 508

import Definitions.Def_WildeQIT_Covering_expectation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Notation

open Matrix MeasureTheory
open scoped ComplexOrder

namespace WildeQIT.Covering

/-- **Lemma 17.3.2 (Operator Markov Inequality)** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, eq. (17.19), p. 508). Let `X ∈ L(H)` be a positive semi-definite
operator-valued random variable with expectation `E{X}`, and let `A` be a fixed positive
definite operator. Then `Pr{X ≰ A} ≤ Tr{E{X} A⁻¹}`.

**Formalization Note.** `H` is finite-dimensional, operators are matrices over a finite index
type. The random variable is a map `X : Ω → Matrix n n ℂ` on a probability space `(Ω, μ)`, positive
semi-definite at every outcome. `E{X}` is the entrywise expectation `WildeQIT.Covering.expectation`;
its entries are assumed integrable, which the book presupposes when it writes `E{X}`. `X ≰ A` is
`¬ (A − X).PosSemidef`; the probability is the (outer) measure of that event, as a real number.
`A⁻¹` is the matrix inverse; `Tr{E{X}A⁻¹}`, real here, is the real part of the complex trace. -/
theorem lemma_17_3_2 {Ω n : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℂ) (hX : ∀ ω, (X ω).PosSemidef)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ)
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    (μ {ω | ¬ (A - X ω).PosSemidef}).toReal ≤ (expectation μ X * A⁻¹).trace.re := by sorry

end WildeQIT.Covering
