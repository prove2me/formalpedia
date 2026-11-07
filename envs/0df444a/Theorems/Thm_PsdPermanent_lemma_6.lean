-- Prove2me | Theorems.Thm_PsdPermanent_lemma_6
-- name    : PsdPermanent.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:33.738195+00:00
-- url     : https://prove2.me/theorems/f60f0b6a-275b-40cc-a582-2945159a86ab
-- title:
--   Lemma 6 — Wick formula for PSD permanents
-- statement:
--   Let $A=VV^\dagger$, with rows $v_1^\dagger,\dots,v_n^\dagger$, and let $Z\sim\mathcal{CN}(0,I_d)$. Then both integrands below are integrable and
--   $$\mathrm{per}(A)=\mathbb E\Big[\prod_{i=1}^n|v_i^\dagger Z|^2\Big]=\frac1{\pi^d}\int_{\mathbb C^d}\prod_{i=1}^n|v_i^\dagger z|^2e^{-z^\dagger z}\,dz.$$
--
--   This is the representation that the variational argument starts from, and it shows that $\mathrm{per}(A)\ge0$.
--
--   Differences from the source:
--   - generalization: V of full column rank, in the §3 convention → any V : ℂ^{n×d}; reason: the formula needs no rank condition; full column rank factors are a special case
--   - encoding: per(A) = ∑_σ ∏_i A_{i,σ(i)}, a real number on PSD A → Mathlib permanent in ℂ, equal to the cast of a real integral; reason: the same value
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 6, p.6

import Mathlib
import Definitions.Def_PsdPermanent_cnDensity
import Definitions.Def_PsdPermanent_secondMoment
open Matrix
open MeasureTheory

namespace PsdPermanent

/-- **Lemma 6 (Wick formula for PSD permanents).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 6, p.6: "Let A = V V† ⪰ 0, with rows v_1, . . . , v_n, and let Z ∼ CN(0, I_d). Then per(A) =
E[∏_{i=1}^n |v_i† Z|²] = (1/π^d) ∫_{C^d} ∏_{i=1}^n |v_i† z|² e^{−z†z} dz."

**Formalization Note.** Stated for any `V`, with no rank hypothesis. The expectation is the integral against
`cnDensity 1`. An equality in `ℂ`, so it also says that `per(A)` is a nonnegative real. Integrability of both integrands
is part of the conclusion. -/
theorem lemma_6 {n d : ℕ} (V : Matrix (Fin n) (Fin d) ℂ) :
    Integrable (fun z : Fin d → ℂ => (∏ i, Complex.normSq ((V *ᵥ z) i)) * cnDensity 1 z) ∧
      Integrable (fun z : Fin d → ℂ => (∏ i, Complex.normSq ((V *ᵥ z) i)) * Real.exp (-zDaggerZ z)) ∧
      (V * Vᴴ).permanent =
        ((∫ z : Fin d → ℂ, (∏ i, Complex.normSq ((V *ᵥ z) i)) * cnDensity 1 z : ℝ) : ℂ) ∧
      (V * Vᴴ).permanent =
        (((Real.pi ^ d)⁻¹ * ∫ z : Fin d → ℂ, (∏ i, Complex.normSq ((V *ᵥ z) i)) * Real.exp (-zDaggerZ z) : ℝ) : ℂ) := by sorry

end PsdPermanent
