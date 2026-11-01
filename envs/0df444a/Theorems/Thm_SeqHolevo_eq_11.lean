-- Prove2me | Theorems.Thm_SeqHolevo_eq_11
-- name    : SeqHolevo.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:02:37.124887+00:00
-- url     : https://prove2.me/theorems/967ab1ed-af33-45d9-afa5-85056a35714e
-- title:
--   Eq. (11) — smoothed upper bound on the expected error (8)
-- statement:
--   Let the codebook be random ($|\mathcal M|=M\ge1$ codewords drawn i.i.d. from $p_{X^n}$) and the message uniform. Let $\Pi$ be an orthogonal projector and $\varepsilon$ a number for which (9) and (10) hold. Then the expected error (8) of the sequential decoder satisfies
--
--   $$1-\mathbb E\operatorname{Tr}\{\varphi_{X^n(M)}\hat\Pi_{M-1}\cdots\hat\Pi_1\varphi_{X^n(M)}\hat\Pi_1\cdots\hat\Pi_{M-1}\varphi_{X^n(M)}\}\le\mathbb E\operatorname{Tr}\{\Pi\varphi_{X^n(M)}\Pi\}-\mathbb E\operatorname{Tr}\{\varphi_{X^n(M)}\hat\Pi_{M-1}\cdots\hat\Pi_1\Pi\varphi_{X^n(M)}\Pi\hat\Pi_1\cdots\hat\Pi_{M-1}\varphi_{X^n(M)}\}+\varepsilon+2\sqrt\varepsilon ,$$
--
--   with $\hat\Pi_i=I^{\otimes n}-\varphi_{X^n(i)}$, and every expectation is of an integrable function.
--
--   This is the step that replaces the true channel outputs by their projections onto the typical subspace, at a cost $\varepsilon+2\sqrt\varepsilon$.
--
--   The channel $x\mapsto|\varphi_x\rangle$ is a family of unit vectors $W(x)\in\ell^2(I)$ for an arbitrary index set $I$ (so the output Hilbert space is arbitrary, infinite-dimensional allowed), the input space $X$ is any measurable space (discrete or continuous), $p_X$ is any probability measure $\mu$ on $X$ for which the matrix entries of $x\mapsto|\varphi_x\rangle\langle\varphi_x|$ are measurable, $\rho=\int|\varphi_x\rangle\langle\varphi_x|\,d\mu(x)$ (coefficientwise), and $H(\rho)<\infty$ (von Neumann entropy in bits).
--
--   Differences from the source:
--   - encoding: a distribution p_X(x), x discrete or continuous; ρ ≡ Σ_x p_X(x)|φ_x⟩⟨φ_x| → any probability measure μ on any measurable space X with measurable matrix entries of x ↦ |φ_x⟩⟨φ_x|; ρ = meanOutput W μ (coefficientwise integral); reason: a sum over a discrete X is the integral against a discrete μ; measurability of the entries is what makes ρ and the random codebook defined, and is automatic for a discrete X
--   - encoding: pure states |φ_x⟩ of a Hilbert space; |φ_{xⁿ}⟩ = |φ_{x_1}⟩ ⊗ ⋯ ⊗ |φ_{x_n}⟩ → unit coefficient vectors W x on ℓ²(I) for an arbitrary I : Type; productPureCQChannel W n on the product basis Fin n → I; reason: every Hilbert space has an orthonormal basis, and the product basis indexes the completed tensor product; no finiteness or countability is imposed
--   - reading: H(ρ) used as a real number (rate "H(ρ) bits per channel use") → hypothesis kernelEntropyBits (meanOutput W μ) ≠ ⊤; reason: the rate H(ρ) and the proof's |H̄(xⁿ) − H(X)| ≤ δ require a finite entropy
--   - generalization: Π the typical projector and ε, n as in (9)–(10) ("n sufficiently large") → any n, M ≥ 1, orthogonal projector Π and ε for which (9) and (10) hold (hypotheses h9, h10); reason: the derivation of (11) uses only (9), (10) and Lemma 8; the paper's Π and n satisfy them by (9)–(10)
--   - encoding: expectation over the random codebook (codewords i.i.d. p_{Xⁿ}) and a uniformly random message M ∈ {1, …, |𝓜|} → Bochner integral against codebookLaw μ n M = (μ^{⊗n})^{⊗M} of the message average (1/M) Σ_m, with M ≥ 1, each asserted with integrability; reason: the same expectation; the integrability conjuncts exclude Lean's default value 0 for a non-integrable function
--   - encoding: messages 1, …, |𝓜| and tests Π̂_1, …, Π̂_{M−1} before message M → Fin M, 0-based: message m is preceded by the tests of codewords 0, …, m − 1; reason: relabelling only
--   - encoding: traces of products of rank-one operators φ = |φ⟩⟨φ| and the projector Π → vector forms: Tr{ΠφΠ} = ‖Π|φ⟩‖², Tr{Π̂_m ΠφΠ} = ‖Π|φ_m⟩‖² − |⟨φ_m|Π|φ_m⟩|², Tr{φ_i Π φ_m Π} = |⟨φ_i|Π|φ_m⟩|², and the sequential terms as |⟨φ_m|Π̂_{m−1}⋯Π̂_1(Π)|φ_m⟩|²; reason: identities for unit vectors and self-adjoint Π; the same numbers
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, eq. (11), p.7

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
import Definitions.Def_SeqHolevo_smoothedSeqSuccess
import Definitions.Def_SeqHolevo_codeAvgError

open MeasureTheory
open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector coefficientInner meanOutput kernelEntropyBits productPureCQChannel)
open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, eq. (11), p.7 (PDF page): "Using the above observations and the facts that
[(9), (10)] ..., we obtain the following upper bound on (8):
`E Tr{Π φ_{Xⁿ(M)} Π} − E Tr{φ_{Xⁿ(M)} Π̂_{M−1} ⋯ Π̂_1 Π φ_{Xⁿ(M)} Π Π̂_1 ⋯ Π̂_{M−1} φ_{Xⁿ(M)}} + ε + 2√ε`."

For every blocklength `n`, number of messages `M ≥ 1`, orthogonal projector `Π` and `ε` for which
(9) and (10) hold, the expected average error (8) of the sequential decoder of the random code is
at most the displayed quantity.

**Formalization Note.** The channel `x ↦ |φ_x⟩` is `W : X → I → ℂ` (unit coefficient vectors on ℓ²(I), any measurable
space `X`, any index type `I`), `p_X` is any probability measure `μ`, the matrix entries of
`x ↦ |φ_x⟩⟨φ_x|` are measurable, `ρ = meanOutput W μ`, and `hfin` says `H(ρ) < ∞` (published
`Intakenext100.P76` objects; see `theorem_1`). The random codebook `C : Fin M → Fin n → X` has the
law `codebookLaw μ n M = (p_{Xⁿ})^{⊗M}` and the message is uniform on `Fin M` (weights `1/M`,
`M ≥ 1`); `|φ_{Xⁿ(m)}⟩ = codeVecs W n C m`. Expectations are Bochner integrals asserted together
with integrability (no default-zero integral). Messages and tests are 0-based: the paper's
`Π̂_1, …, Π̂_{M−1}` before message `M` are Lean's tests `0, …, m−1` before message `m`. (9) and (10) are hypotheses `h9`, `h10` (with `Π φ Π =
|Πφ⟩⟨Πφ|`, `‖·‖₁ = traceSize`, `Π̂ = I − Π`), so the statement holds for any projector satisfying
them (a generalization: the paper's `Π` is the typical projector). (8) is
`E_C codeAvgError`, `Tr{Π φ Π} = ‖Π|φ⟩‖²`, and the second expectation is `smoothedSeqSuccess`. -/
theorem eq_11 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {I : Type}
    (W : X → I → ℂ) (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (hfin : kernelEntropyBits (meanOutput W μ) ≠ ⊤)
    (n M : ℕ) (hM : 0 < M) (P : Matrix (Fin n → I) (Fin n → I) ℂ) (hP : IsOrthProjector P)
    (ε : ℝ)
    (h9 : ∫⁻ x, traceSize
      (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x)) -
        Matrix.vecMulVec (arrApply P (productPureCQChannel W n x))
          (star (arrApply P (productPureCQChannel W n x))))
      ∂(Measure.pi fun _ : Fin n => μ) ≤ ENNReal.ofReal (2 * Real.sqrt ε))
    (h10 : realFockTracePair (idArr (Fin n → I) - P) (HolevoCQ.tensorPowMat (meanOutput W μ) n) ≤ ε) :
    Integrable (fun C : Fin M → Fin n → X => codeAvgError W n C) (codebookLaw μ n M) ∧
    Integrable (fun C : Fin M → Fin n → X => (∑ m, vecNormSq (arrApply P (codeVecs W n C m))) / M) (codebookLaw μ n M) ∧
    Integrable (fun C : Fin M → Fin n → X => (∑ m, smoothedSeqSuccess (codeVecs W n C) P m) / M) (codebookLaw μ n M) ∧
    ∫ C, codeAvgError W n C ∂(codebookLaw μ n M) ≤
      (∫ C, (fun C : Fin M → Fin n → X => (∑ m, vecNormSq (arrApply P (codeVecs W n C m))) / M) C ∂(codebookLaw μ n M)) -
        (∫ C, (fun C : Fin M → Fin n → X => (∑ m, smoothedSeqSuccess (codeVecs W n C) P m) / M) C ∂(codebookLaw μ n M)) + ε + 2 * Real.sqrt ε := by sorry

end SeqHolevo
