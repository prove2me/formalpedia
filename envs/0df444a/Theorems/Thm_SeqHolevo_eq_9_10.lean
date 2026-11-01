-- Prove2me | Theorems.Thm_SeqHolevo_eq_9_10
-- name    : SeqHolevo.eq_9_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:00:38.264033+00:00
-- url     : https://prove2.me/theorems/e027b738-d446-4fd1-9df6-a993eb36f44e
-- title:
--   Eqs. (9)–(10) — the typical projector is gentle and captures almost all of $\rho^{\otimes n}$
-- statement:
--   Fix $\delta>0$ and $\varepsilon>0$. For all sufficiently large $n$, the typical projector $\Pi=\Pi^n_{\rho,\delta}$ of $\rho$ satisfies
--
--   $$\mathbb E\,\big\|\varphi_{X^n}-\Pi\varphi_{X^n}\Pi\big\|_1\le2\sqrt\varepsilon\quad(9),\qquad \operatorname{Tr}\{\hat\Pi\rho^{\otimes n}\}\le\varepsilon\quad(10),$$
--
--   where $x^n\sim p_{X^n}$ and $\hat\Pi=I-\Pi$. The threshold for $n$ depends on $\delta$, $\varepsilon$ and the channel only, and the statement holds for the typical projector built from any spectral decomposition of $\rho$.
--
--   These are the inputs from typicality (Appendix A) and the gentle operator lemma (Lemma 9) to the error analysis.
--
--   The channel $x\mapsto|\varphi_x\rangle$ is a family of unit vectors $W(x)\in\ell^2(I)$ for an arbitrary index set $I$ (so the output Hilbert space is arbitrary, infinite-dimensional allowed), the input space $X$ is any measurable space (discrete or continuous), $p_X$ is any probability measure $\mu$ on $X$ for which the matrix entries of $x\mapsto|\varphi_x\rangle\langle\varphi_x|$ are measurable, $\rho=\int|\varphi_x\rangle\langle\varphi_x|\,d\mu(x)$ (coefficientwise), and $H(\rho)<\infty$ (von Neumann entropy in bits).
--
--   Differences from the source:
--   - encoding: a distribution p_X(x), x discrete or continuous; ρ ≡ Σ_x p_X(x)|φ_x⟩⟨φ_x| → any probability measure μ on any measurable space X with measurable matrix entries of x ↦ |φ_x⟩⟨φ_x|; ρ = meanOutput W μ (coefficientwise integral); reason: a sum over a discrete X is the integral against a discrete μ; measurability of the entries is what makes ρ and the random codebook defined, and is automatic for a discrete X
--   - encoding: pure states |φ_x⟩ of a Hilbert space; |φ_{xⁿ}⟩ = |φ_{x_1}⟩ ⊗ ⋯ ⊗ |φ_{x_n}⟩ → unit coefficient vectors W x on ℓ²(I) for an arbitrary I : Type; productPureCQChannel W n on the product basis Fin n → I; reason: every Hilbert space has an orthonormal basis, and the product basis indexes the completed tensor product; no finiteness or countability is imposed
--   - reading: H(ρ) used as a real number (rate "H(ρ) bits per channel use") → hypothesis kernelEntropyBits (meanOutput W μ) ≠ ⊤; reason: the rate H(ρ) and the proof's |H̄(xⁿ) − H(X)| ≤ δ require a finite entropy
--   - reading: "for all ε > 0 whenever n is sufficiently large", δ fixed by the typical projector → ∀ δ > 0, ∀ ε > 0, ∃ N, ∀ n ≥ N; reason: δ is chosen with Π before ε; N may depend on ε, δ and the channel, not on any code
--   - encoding: Π^n_{ρ,δ} built from the spectral decomposition of ρ → for every spectral decomposition (p, u) of ρ, with the same N; reason: the typical subspace of ρ^{⊗n} is a spectral subspace, independent of the chosen eigenbasis, so all choices give the same Π
--   - encoding: E‖φ − ΠφΠ‖₁ → lower Lebesgue integral of traceSize (φ − |Πφ⟩⟨Πφ|) with an a.e.-measurability conjunct; reason: ΠφΠ = |Πφ⟩⟨Πφ| for self-adjoint Π; nonnegative integrand
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, eqs. (9)–(10), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrApply
import Definitions.Def_SeqHolevo_vecNormSq
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_SeqHolevo_IsOrthProjector
import Definitions.Def_SeqHolevo_IsSpectralDecomp
import Definitions.Def_SeqHolevo_typicalProjector

open MeasureTheory
open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector coefficientInner meanOutput kernelEntropyBits productPureCQChannel)
open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, eqs. (9)–(10), p.7 (PDF page): "Using the above observations and the facts
that `E ‖φ_{Xⁿ(M)} − Π φ_{Xⁿ(M)} Π‖₁ ≤ 2√ε` (9), `Tr{Π̂ ρ^{⊗n}} ≤ ε` (10), for all `ε > 0` whenever
`n` is sufficiently large (these are from the properties of typicality and Lemma 9)".

For every `δ > 0` and `ε > 0` there is `N` such that for every `n ≥ N` and every spectral
decomposition `(p, u)` of `ρ`, the typical projector `Π = Π^n_{ρ,δ}` satisfies (9) and (10).

**Formalization Note.** The channel `x ↦ |φ_x⟩` is `W : X → I → ℂ` (unit coefficient vectors on ℓ²(I), any measurable
space `X`, any index type `I`), `p_X` is any probability measure `μ`, the matrix entries of
`x ↦ |φ_x⟩⟨φ_x|` are measurable, `ρ = meanOutput W μ`, and `hfin` says `H(ρ) < ∞` (published
`Intakenext100.P76` objects; see `theorem_1`). `p_{Xⁿ}` is `Measure.pi (fun _ => μ)` and
`|φ_{xⁿ}⟩` is `productPureCQChannel W n xⁿ` on the product basis `Fin n → I`. Expectations are
Bochner integrals asserted together with integrability (no default-zero integral). `Π φ Π = |Π φ_{xⁿ}⟩⟨Π φ_{xⁿ}|` and `‖·‖₁` is the published
`traceSize` (`ℝ≥0∞`); the expectation in (9) is a lower Lebesgue integral, asserted with the
a.e.-measurability of its integrand. `N` depends on `δ`, `ε` and the channel only, not on the
decomposition (the typical subspace of `ρ^{⊗n}` is a spectral subspace, independent of the chosen
eigenbasis) and not on any code. `Π̂ = I − Π`. -/
theorem eq_9_10 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {I : Type}
    (W : X → I → ℂ) (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (hfin : kernelEntropyBits (meanOutput W μ) ≠ ⊤) :
    ∀ δ > 0, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ (p : ℕ → ℝ) (u : ℕ → I → ℂ),
      IsSpectralDecomp (meanOutput W μ) p u →
      (AEMeasurable (fun x => traceSize
          (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x)) -
            Matrix.vecMulVec (arrApply (typicalProjector p u n δ) (productPureCQChannel W n x))
              (star (arrApply (typicalProjector p u n δ) (productPureCQChannel W n x)))))
          (Measure.pi fun _ : Fin n => μ) ∧
        ∫⁻ x, traceSize
          (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x)) -
            Matrix.vecMulVec (arrApply (typicalProjector p u n δ) (productPureCQChannel W n x))
              (star (arrApply (typicalProjector p u n δ) (productPureCQChannel W n x))))
          ∂(Measure.pi fun _ : Fin n => μ) ≤ ENNReal.ofReal (2 * Real.sqrt ε)) ∧
      realFockTracePair (idArr (Fin n → I) - typicalProjector p u n δ)
        (HolevoCQ.tensorPowMat (meanOutput W μ) n) ≤ ε := by sorry

end SeqHolevo
