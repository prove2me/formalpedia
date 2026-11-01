-- Prove2me | Theorems.Thm_SeqHolevo_second_term_bound
-- name    : SeqHolevo.second_term_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:00:11.745173+00:00
-- url     : https://prove2.me/theorems/447476fa-f1da-4c58-9741-8ba108698cb9
-- title:
--   Appendix B, p.7 — bound on the second term, $\le2^{-n[H(\rho)-\delta]}|\mathcal M|$
-- statement:
--   Let $\delta>0$, let $\Pi=\Pi^n_{\rho,\delta}$ be the typical projector of $\rho$, and consider a random codebook with $M\ge1$ codewords drawn i.i.d. from $p_{X^n}$ and a uniform message. Then
--
--   $$\mathbb E\sum_{i=1}^{M-1}\operatorname{Tr}\{\varphi_{X^n(i)}\Pi\varphi_{X^n(M)}\Pi\}\le2^{-n[H(\rho)-\delta]}\,|\mathcal M| ,$$
--
--   and the expectation is of an integrable function. Independence of the codewords turns each term into $\operatorname{Tr}\{\rho^{\otimes n}\Pi\rho^{\otimes n}\Pi\}$, which the eigenvalue bound on the typical subspace controls. This bounds the second term under the square root in Sen's bound.
--
--   The channel $x\mapsto|\varphi_x\rangle$ is a family of unit vectors $W(x)\in\ell^2(I)$ for an arbitrary index set $I$ (so the output Hilbert space is arbitrary, infinite-dimensional allowed), the input space $X$ is any measurable space (discrete or continuous), $p_X$ is any probability measure $\mu$ on $X$ for which the matrix entries of $x\mapsto|\varphi_x\rangle\langle\varphi_x|$ are measurable, $\rho=\int|\varphi_x\rangle\langle\varphi_x|\,d\mu(x)$ (coefficientwise), and $H(\rho)<\infty$ (von Neumann entropy in bits).
--
--   Differences from the source:
--   - encoding: a distribution p_X(x), x discrete or continuous; ρ ≡ Σ_x p_X(x)|φ_x⟩⟨φ_x| → any probability measure μ on any measurable space X with measurable matrix entries of x ↦ |φ_x⟩⟨φ_x|; ρ = meanOutput W μ (coefficientwise integral); reason: a sum over a discrete X is the integral against a discrete μ; measurability of the entries is what makes ρ and the random codebook defined, and is automatic for a discrete X
--   - encoding: pure states |φ_x⟩ of a Hilbert space; |φ_{xⁿ}⟩ = |φ_{x_1}⟩ ⊗ ⋯ ⊗ |φ_{x_n}⟩ → unit coefficient vectors W x on ℓ²(I) for an arbitrary I : Type; productPureCQChannel W n on the product basis Fin n → I; reason: every Hilbert space has an orthonormal basis, and the product basis indexes the completed tensor product; no finiteness or countability is imposed
--   - reading: H(ρ) used as a real number (rate "H(ρ) bits per channel use") → hypothesis kernelEntropyBits (meanOutput W μ) ≠ ⊤; reason: the rate H(ρ) and the proof's |H̄(xⁿ) − H(X)| ≤ δ require a finite entropy
--   - encoding: expectation over the random codebook (codewords i.i.d. p_{Xⁿ}) and a uniformly random message M ∈ {1, …, |𝓜|} → Bochner integral against codebookLaw μ n M = (μ^{⊗n})^{⊗M} of the message average (1/M) Σ_m, with M ≥ 1, each asserted with integrability; reason: the same expectation; the integrability conjuncts exclude Lean's default value 0 for a non-integrable function
--   - encoding: messages 1, …, |𝓜| and tests Π̂_1, …, Π̂_{M−1} before message M → Fin M, 0-based: message m is preceded by the tests of codewords 0, …, m − 1; reason: relabelling only
--   - encoding: traces of products of rank-one operators φ = |φ⟩⟨φ| and the projector Π → vector forms: Tr{ΠφΠ} = ‖Π|φ⟩‖², Tr{Π̂_m ΠφΠ} = ‖Π|φ_m⟩‖² − |⟨φ_m|Π|φ_m⟩|², Tr{φ_i Π φ_m Π} = |⟨φ_i|Π|φ_m⟩|², and the sequential terms as |⟨φ_m|Π̂_{m−1}⋯Π̂_1(Π)|φ_m⟩|²; reason: identities for unit vectors and self-adjoint Π; the same numbers
--   - encoding: H(ρ), and Π^n_{ρ,δ} built from the spectral decomposition of ρ → H(ρ) = (kernelEntropyBits ρ).toReal; Π = typicalProjector p u n δ for any spectral decomposition (p, u) of ρ; reason: H(ρ) equals the H(X) of every spectral decomposition, and the typical subspace does not depend on the chosen eigenbasis
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, p.7, unnumbered display "For the second term, consider that …"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrApply
import Definitions.Def_SeqHolevo_vecNormSq
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_SeqHolevo_IsOrthProjector
import Definitions.Def_SeqHolevo_codebookLaw
import Definitions.Def_SeqHolevo_codeVecs
import Definitions.Def_SeqHolevo_IsSpectralDecomp
import Definitions.Def_SeqHolevo_typicalProjector

open MeasureTheory
open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector coefficientInner meanOutput kernelEntropyBits productPureCQChannel)
open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.7 (PDF page; unnumbered display): "For the second term, consider that
`E Σ_{i=1}^{M−1} Tr{φ_{Xⁿ(i)} Π φ_{Xⁿ(M)} Π} ≤ E_M Σ_{i≠M} E_{Xⁿ} Tr{φ_{Xⁿ(i)} Π φ_{Xⁿ(M)} Π} = ⋯
= Σ_{i≠M} Tr{ρ^{⊗n} Π ρ^{⊗n} Π} ≤ 2^{−n[H(ρ)−δ]} Σ_{i≠M} Tr{ρ^{⊗n} Π} ≤ 2^{−n[H(ρ)−δ]} |𝓜|`."

For every `δ > 0`, `n`, `M ≥ 1` and the typical projector `Π = Π^n_{ρ,δ}` of any spectral
decomposition of `ρ`: `E Σ_{i<m} Tr{φ_{Xⁿ(i)} Π φ_{Xⁿ(m)} Π} ≤ 2^{−n[H(ρ)−δ]} |𝓜|`.

**Formalization Note.** The channel `x ↦ |φ_x⟩` is `W : X → I → ℂ` (unit coefficient vectors on ℓ²(I), any measurable
space `X`, any index type `I`), `p_X` is any probability measure `μ`, the matrix entries of
`x ↦ |φ_x⟩⟨φ_x|` are measurable, `ρ = meanOutput W μ`, and `hfin` says `H(ρ) < ∞` (published
`Intakenext100.P76` objects; see `theorem_1`). The random codebook `C : Fin M → Fin n → X` has the
law `codebookLaw μ n M = (p_{Xⁿ})^{⊗M}` and the message is uniform on `Fin M` (weights `1/M`,
`M ≥ 1`); `|φ_{Xⁿ(m)}⟩ = codeVecs W n C m`. Expectations are Bochner integrals asserted together
with integrability (no default-zero integral). Messages and tests are 0-based: the paper's
`Π̂_1, …, Π̂_{M−1}` before message `M` are Lean's tests `0, …, m−1` before message `m`. `Tr{φ_i Π φ_m Π} = |⟨Φ_i, ΠΦ_m⟩|²`; `H(ρ)` is written as printed,
`(kernelEntropyBits ρ).toReal` (finite by `hfin`), which equals the `H(X)` of every spectral
decomposition used to build `Π`. The bound keeps the printed `|𝓜|` (the sum has `m ≤ M − 1`
terms). -/
theorem second_term_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {I : Type}
    (W : X → I → ℂ) (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (hfin : kernelEntropyBits (meanOutput W μ) ≠ ⊤)
    (δ : ℝ) (hδ : 0 < δ) (n M : ℕ) (hM : 0 < M) (p : ℕ → ℝ) (u : ℕ → I → ℂ)
    (hdec : IsSpectralDecomp (meanOutput W μ) p u) :
    Integrable (fun C : Fin M → Fin n → X => (∑ m : Fin M, ∑ i ∈ Finset.Iio m,
          Complex.normSq (coefficientInner (codeVecs W n C i) (arrApply (typicalProjector p u n δ) (codeVecs W n C m)))) / M) (codebookLaw μ n M) ∧
    ∫ C, (fun C : Fin M → Fin n → X => (∑ m : Fin M, ∑ i ∈ Finset.Iio m,
          Complex.normSq (coefficientInner (codeVecs W n C i) (arrApply (typicalProjector p u n δ) (codeVecs W n C m)))) / M) C ∂(codebookLaw μ n M) ≤
      (2 : ℝ) ^ (-((n : ℝ) * ((kernelEntropyBits (meanOutput W μ)).toReal - δ))) * M := by sorry

end SeqHolevo
