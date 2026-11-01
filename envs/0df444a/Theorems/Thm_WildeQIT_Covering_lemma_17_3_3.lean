-- Prove2me | Theorems.Thm_WildeQIT_Covering_lemma_17_3_3
-- name    : WildeQIT.Covering.lemma_17_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:18.349345+00:00
-- url     : https://prove2.me/theorems/969b9326-2222-4115-96d0-a2018d363d1d
-- title:
--   Bernstein trick: $\Pr\{\sum_k X_k\not\le KA\}\le\dim(\mathcal H)\,\|\mathbb E\{e^{T(X-A)T^\dagger}\}\|_\infty^K$
-- statement:
--   **Lemma 17.3.3 (Bernstein Trick).** Let $\mathcal H$ be a finite-dimensional Hilbert space, and let $X,X_1,\dots,X_K$ be independent, identically distributed Hermitian operator-valued random variables on $\mathcal H$. Let $A$ be a fixed Hermitian operator. Then for every invertible operator $T$,
--
--   $$\Pr\Bigl\{\sum_{k=1}^KX_k\not\le KA\Bigr\}\le\dim(\mathcal H)\,\Bigl\|\mathbb E\bigl\{\exp\{T(X-A)T^\dagger\}\bigr\}\Bigr\|_\infty^K .$$
--
--   Here $\exp\{B\}=\sum_ie^{b_i}|i\rangle\langle i|$ for a Hermitian $B=\sum_ib_i|i\rangle\langle i|$, $\|\cdot\|_\infty$ is the operator norm, and $B\not\le C$ means that $C-B$ is not positive semi-definite.
--
--   It reduces a tail bound for a sum of independent random operators to the norm of a single matrix moment generating function, and it is the second step towards the operator Chernoff bound.
--
--   **Formalization Note** $\mathcal H=\mathbb C^n$, $\dim\mathcal H=|n|$. The random operators are maps from a probability space to matrices, which carry the entrywise Borel σ-algebra; $X_1,\dots,X_K$ are mutually independent and each has the law of $X$. The exponential is the spectral one (continuous functional calculus of $\exp$), as on p. 508. The entries of $\exp\{T(X-A)T^\dagger\}$ are assumed integrable.
--
--   Differences from the source:
--   - generalization: $X,X_1,\dots,X_K$ i.i.d. → $X_1,\dots,X_K$ mutually independent, each with the law of $X$, with no independence of $X$ from them; reason: the right side depends on $X$ only through its law, and an i.i.d. family $X,X_1,\dots,X_K$ satisfies these hypotheses.
--   - encoding: the expectation $\mathbb E\{\exp\{T(X-A)T^\dagger\}\}$ → entrywise integral with integrable entries; reason: integrability only excludes the case where the expectation is infinite and the bound holds trivially; Lean's integral would return $0$ there.
--   - encoding: $B\not\le C$ → $C-B$ not positive semi-definite; reason: the book's definition of the operator order (p. 508).
--   - encoding: $\Pr\{\sum_kX_k\not\le KA\}$ for measurable random variables → the measure of the set $\{\omega : KA-\sum_kX_k(\omega)\text{ not PSD}\}$, with no measurability hypothesis beyond what `IdentDistrib` gives; reason: `IdentDistrib` makes each $X_k$ almost-everywhere measurable, so the event is null-measurable and its measure is the book's probability.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 17.3.3 (Bernstein Trick), eq. (17.23), p. 509

import Definitions.Def_WildeQIT_Covering_expectation
import Definitions.Def_WildeQIT_Covering_matrixMeasurableSpace
import Definitions.Def_WildeQIT_Covering_opNorm
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder MatrixOrder

attribute [local instance] WildeQIT.Covering.matrixMeasurableSpace

namespace WildeQIT.Covering

/-- **Lemma 17.3.3 (Bernstein Trick)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, eq. (17.23), p. 509). Let `X, X₁, …, X_K ∈ L(H)` be i.i.d. Hermitian
operator-valued random variables, and let `A` be a fixed Hermitian operator. Then for any
invertible operator `T`,
`Pr{∑_{k=1}^K X_k ≰ K A} ≤ dim(H) ‖E{exp{T(X − A)T†}}‖_∞^K`.

**Formalization Note.** `H = ℂⁿ` for a finite index type `n`, so `dim(H) = |n|`. The random
operators are maps `Ω → Matrix n n ℂ` on a probability space, Hermitian at every outcome;
matrices carry the entrywise Borel σ-algebra `matrixMeasurableSpace`. `X₁, …, X_K` (indexed by
`Fin K`) are mutually independent and each has the law of `X`; independence of `X` from
`X₁, …, X_K` is not required (the right side depends on `X` only through its law), so the
statement covers the book's i.i.d. family `X, X₁, …, X_K`. `exp{·}` of a Hermitian operator is
the spectral exponential `∑ᵢ exp(aᵢ)|i⟩⟨i|` (the book's convention on p. 508), i.e. the continuous
functional calculus `cfc Real.exp`. `E{·}` is the entrywise expectation; the entries of
`exp{T(X − A)T†}` are assumed integrable, which the book presupposes when it writes the expectation
(otherwise the right side would be infinite). `B ≰ C` is `¬ (C − B).PosSemidef`; `‖·‖_∞` is the
operator norm `WildeQIT.Covering.opNorm`. -/
theorem lemma_17_3_3 {Ω n : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ℕ)
    (X : Ω → Matrix n n ℂ) (Xs : Fin K → Ω → Matrix n n ℂ)
    (hXherm : ∀ ω, (X ω).IsHermitian) (hXsherm : ∀ k ω, (Xs k ω).IsHermitian)
    (hindep : iIndepFun Xs μ) (hident : ∀ k, IdentDistrib (Xs k) X μ μ)
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (T : Matrix n n ℂ) (hT : IsUnit T)
    (hint : ∀ i j, Integrable (fun ω => cfc Real.exp (T * (X ω - A) * Tᴴ) i j) μ) :
    (μ {ω | ¬ ((K : ℂ) • A - ∑ k, Xs k ω).PosSemidef}).toReal ≤
      (Fintype.card n : ℝ) *
        opNorm (expectation μ (fun ω => cfc Real.exp (T * (X ω - A) * Tᴴ))) ^ K := by sorry

end WildeQIT.Covering
