-- Prove2me | Theorems.Thm_SeqHolevo_lemma_9
-- name    : SeqHolevo.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:15.00901+00:00
-- url     : https://prove2.me/theorems/fa9f8071-b049-4c1f-95da-4191b2ef1c15
-- title:
--   Lemma 9 — gentle operator lemma for ensembles
-- statement:
--   Let $\nu$ be an ensemble of density operators (a probability distribution over states $\rho_X$) with expected density operator $\rho=\mathbb E\,\rho_X$, and let $\Lambda$ be an operator with $I\ge\Lambda\ge0$ that succeeds with high probability on $\rho$: $\operatorname{Tr}\{\Lambda\rho\}\ge1-\varepsilon$. Then the subnormalized states $\sqrt\Lambda\rho_X\sqrt\Lambda$ are close to the originals in expected trace distance:
--
--   $$\mathbb E_X\big\|\sqrt\Lambda\,\rho_X\sqrt\Lambda-\rho_X\big\|_1\le2\sqrt\varepsilon .$$
--
--   Here $\sqrt\Lambda$ is the positive square root. Appendix B applies it with $\Lambda=\Pi$ (the typical projector) to the ensemble $\{p_{X^n}(x^n),\varphi_{x^n}\}$ to obtain (9).
--
--   Differences from the source:
--   - generalization: a discrete ensemble {p_X(x), ρ_x} → any probability measure ν on density operators (Borel for the trace norm) with barycenter ρ; reason: a discrete ensemble is ν = Σ_x p_X(x) δ_{ρ_x}; the paper applies the lemma to {p_{Xⁿ}(xⁿ), φ_{xⁿ}}, which is continuous when X is
--   - encoding: √Λ → every S with 0 ≤ S ≤ I and S S = Λ; reason: the positive square root of 0 ≤ Λ ≤ I is the unique such S, so this is the statement about √Λ
--   - encoding: E_X‖·‖₁ → lower Lebesgue integral in ℝ≥0∞ of traceSize, with an a.e.-measurability conjunct; reason: nonnegative integrand; the measurability conjunct makes the integral the true expectation
--   - encoding: operators on a Hilbert space; Tr, ‖·‖₁ and the order ≤ → coefficient arrays on ℓ²(J) for any index type J; Tr[XE] = realFockTracePair X E; ‖·‖₁ = traceSize; ≤ = TraceOperatorLE (finite quadratic forms); reason: published coordinate conventions (Next46.P32, Dependency50.P33, Frontier18.P01); the same operators and numbers
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, Lemma 9, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrMul

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsBarycenter traceSize)
open QAlgorithms.Papers.Independent.Frontier18.P01 (IsPositive TraceOperatorLE)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, Lemma 9 (Gentle Operator Lemma for Ensembles), p.6 (PDF page): "Given an
ensemble `{p_X(x), ρ_x}` with expected density operator `ρ ≡ Σ_x p_X(x) ρ_x`, suppose that an
operator `Λ` such that `I ≥ Λ ≥ 0` succeeds with high probability on the state `ρ`:
`Tr{Λρ} ≥ 1 − ε`. Then the subnormalized state `√Λ ρ_x √Λ` is close in expected trace distance
to the original state `ρ_x`: `E_X{‖√Λ ρ_X √Λ − ρ_X‖₁} ≤ 2√ε`."

**Formalization Note.** The ensemble is a probability measure `ν` on the published space of
density operators `State J` (trace-norm Borel σ-algebra, `Dependency50.P33`) with barycenter `ρ`
(`IsBarycenter`); a discrete ensemble `{p_X(x), ρ_x}` is `ν = Σ_x p_X(x) δ_{ρ_x}` (a
generalization: the paper's proof applies the lemma to the ensemble `{p_{Xⁿ}(xⁿ), φ_{xⁿ}}`, which
is continuous when `X` is). `√Λ` is the positive square root: the conclusion is asserted for every
`S` with `0 ≤ S ≤ I` and `S S = Λ`, and the positive square root of `0 ≤ Λ ≤ I` is the unique
such `S`. `‖·‖₁` is `traceSize` and the expectation a lower Lebesgue integral in `ℝ≥0∞`, together
with the a.e.-measurability of the integrand. -/
theorem lemma_9 {J : Type} (ν : Measure (State J)) [IsProbabilityMeasure ν]
    (ρ Λ : Matrix J J ℂ) (hbar : IsBarycenter ν (fun σ => σ.coefficients) ρ)
    (hΛ : IsPositive Λ) (hΛI : TraceOperatorLE Λ (idArr J))
    (ε : ℝ) (hsucc : 1 - ε ≤ realFockTracePair Λ ρ)
    (S : Matrix J J ℂ) (hS : IsPositive S) (hSI : TraceOperatorLE S (idArr J))
    (hSS : arrMul S S = Λ) :
    AEMeasurable (fun σ : State J =>
      traceSize (arrMul (arrMul S σ.coefficients) S - σ.coefficients)) ν ∧
    ∫⁻ σ, traceSize (arrMul (arrMul S σ.coefficients) S - σ.coefficients) ∂ν ≤
      ENNReal.ofReal (2 * Real.sqrt ε) := by sorry

end SeqHolevo
