-- Prove2me | Theorems.Thm_SeqHolevo_smoothing_identity
-- name    : SeqHolevo.smoothing_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:59:52.93057+00:00
-- url     : https://prove2.me/theorems/864d3316-fa70-49d6-97c6-6940ab67c9c1
-- title:
--   Appendix B, pp.6–7 — the smoothing identity $1=\mathbb E\operatorname{Tr}\{\Pi\varphi\Pi\}+\operatorname{Tr}\{\hat\Pi\rho^{\otimes n}\}$
-- statement:
--   Let $x^n$ be drawn from $p_{X^n}=p_X^{\otimes n}$, let $\varphi_{x^n}=|\varphi_{x^n}\rangle\langle\varphi_{x^n}|$, let $\Pi$ be an orthogonal projector on the $n$-letter output space and $\hat\Pi=I-\Pi$. Then
--
--   $$\begin{aligned}1&=\mathbb E\operatorname{Tr}\{\varphi_{X^n}\}=\mathbb E\operatorname{Tr}\{\Pi\varphi_{X^n}\}+\mathbb E\operatorname{Tr}\{\hat\Pi\varphi_{X^n}\}\\&=\mathbb E\operatorname{Tr}\{\Pi\varphi_{X^n}\Pi\}+\operatorname{Tr}\{\hat\Pi\,\mathbb E\varphi_{X^n}\}=\mathbb E\operatorname{Tr}\{\Pi\varphi_{X^n}\Pi\}+\operatorname{Tr}\{\hat\Pi\rho^{\otimes n}\},\end{aligned}$$
--
--   and in particular $\mathbb E\varphi_{X^n}=\rho^{\otimes n}$. Every expectation is of an integrable function.
--
--   This identity is why projecting the channel outputs onto the typical subspace costs little: the weight lost is $\operatorname{Tr}\{\hat\Pi\rho^{\otimes n}\}$.
--
--   The channel $x\mapsto|\varphi_x\rangle$ is a family of unit vectors $W(x)\in\ell^2(I)$ for an arbitrary index set $I$ (so the output Hilbert space is arbitrary, infinite-dimensional allowed), the input space $X$ is any measurable space (discrete or continuous), $p_X$ is any probability measure $\mu$ on $X$ for which the matrix entries of $x\mapsto|\varphi_x\rangle\langle\varphi_x|$ are measurable, $\rho=\int|\varphi_x\rangle\langle\varphi_x|\,d\mu(x)$ (coefficientwise), and $H(\rho)<\infty$ (von Neumann entropy in bits).
--
--   Differences from the source:
--   - encoding: a distribution p_X(x), x discrete or continuous; ρ ≡ Σ_x p_X(x)|φ_x⟩⟨φ_x| → any probability measure μ on any measurable space X with measurable matrix entries of x ↦ |φ_x⟩⟨φ_x|; ρ = meanOutput W μ (coefficientwise integral); reason: a sum over a discrete X is the integral against a discrete μ; measurability of the entries is what makes ρ and the random codebook defined, and is automatic for a discrete X
--   - encoding: pure states |φ_x⟩ of a Hilbert space; |φ_{xⁿ}⟩ = |φ_{x_1}⟩ ⊗ ⋯ ⊗ |φ_{x_n}⟩ → unit coefficient vectors W x on ℓ²(I) for an arbitrary I : Type; productPureCQChannel W n on the product basis Fin n → I; reason: every Hilbert space has an orthonormal basis, and the product basis indexes the completed tensor product; no finiteness or countability is imposed
--   - reading: H(ρ) used as a real number (rate "H(ρ) bits per channel use") → hypothesis kernelEntropyBits (meanOutput W μ) ≠ ⊤; reason: the rate H(ρ) and the proof's |H̄(xⁿ) − H(X)| ≤ δ require a finite entropy
--   - generalization: Π the typical projector Π^n_{ρ,δ} → any orthogonal projector Π on ℓ²(Iⁿ) (IsOrthProjector); reason: the step uses only that Π is an orthogonal projector; the typical projector is one
--   - encoding: the expectation over the message M and the codeword Xⁿ(M) → the expectation over xⁿ ~ μ^{⊗n}; reason: every codeword has law p_{Xⁿ} whatever the message
--   - encoding: Tr{Π̂ E φ_{Xⁿ}} as a separate link → E Tr{Π̂ φ} = Tr{Π̂ ρ^{⊗n}} together with the conjunct E φ = ρ^{⊗n}; reason: Tr{Π̂ E φ} and Tr{Π̂ ρ^{⊗n}} are the same number once E φ = ρ^{⊗n}
--   - encoding: traces Tr{φ}, Tr{Πφ}, Tr{Π̂φ}, Tr{ΠφΠ} → realFockTracePair I φ, realFockTracePair Π φ, realFockTracePair (I − Π) φ, ‖Π|φ⟩‖²; reason: the same numbers for a unit vector and an orthogonal projector
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, pp.6–7, unnumbered display "1 = E Tr{φ_{Xⁿ(M)}} = … + Tr{Π̂ρ^{⊗n}}"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrApply
import Definitions.Def_SeqHolevo_vecNormSq
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_SeqHolevo_IsOrthProjector

open MeasureTheory
open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector coefficientInner meanOutput kernelEntropyBits productPureCQChannel)
open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, pp.6–7 (PDF pages; unnumbered display): "That we can do so follows from the
fact that `1 = E Tr{φ_{Xⁿ(M)}} = E Tr{Π φ_{Xⁿ(M)}} + E Tr{Π̂ φ_{Xⁿ(M)}}
= E Tr{Π φ_{Xⁿ(M)} Π} + Tr{Π̂ E φ_{Xⁿ(M)}} = E Tr{Π φ_{Xⁿ(M)} Π} + Tr{Π̂ ρ^{⊗n}}`, where
`Π̂ ≡ I − Π`."

The conjuncts state: (a) `E φ_{Xⁿ} = ρ^{⊗n}` coefficientwise; (b) integrability of the four
traces; then each link of the chain: (c) `1 = E Tr{φ}`; (d) `E Tr{φ} = E Tr{Πφ} + E Tr{Π̂φ}`;
(e) `E Tr{Πφ} = E Tr{ΠφΠ}`; (f) `E Tr{Π̂φ} = Tr{Π̂ E φ} = Tr{Π̂ ρ^{⊗n}}`; (g)
`1 = E Tr{ΠφΠ} + Tr{Π̂ ρ^{⊗n}}`.

**Formalization Note.** The channel `x ↦ |φ_x⟩` is `W : X → I → ℂ` (unit coefficient vectors on ℓ²(I), any measurable
space `X`, any index type `I`), `p_X` is any probability measure `μ`, the matrix entries of
`x ↦ |φ_x⟩⟨φ_x|` are measurable, `ρ = meanOutput W μ`, and `hfin` says `H(ρ) < ∞` (published
`Intakenext100.P76` objects; see `theorem_1`). `p_{Xⁿ}` is `Measure.pi (fun _ => μ)` and
`|φ_{xⁿ}⟩` is `productPureCQChannel W n xⁿ` on the product basis `Fin n → I`. Expectations are
Bochner integrals asserted together with integrability (no default-zero integral). `Π` is any orthogonal projector on ℓ²(Iⁿ) (a generalization: the
paper uses the typical projector, and the identity holds for every projector).
`Tr{Π φ Π} = ‖Π|φ⟩‖²` (`vecNormSq`, `arrApply`), `Tr{A X} = realFockTracePair A X` (so
`Tr φ = realFockTracePair I φ`), `φ = |φ_{xⁿ}⟩⟨φ_{xⁿ}|` and `Π̂ = I − Π`; `Tr{Π̂ E φ}` is the same
number as `Tr{Π̂ ρ^{⊗n}}` once (a) identifies `E φ` with `ρ^{⊗n}`.
Since every codeword `Xⁿ(M)` has law `p_{Xⁿ}`, the expectation over the message and the codeword
is the expectation over `xⁿ ~ p_{Xⁿ}`. -/
theorem smoothing_identity {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {I : Type}
    (W : X → I → ℂ) (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (hfin : kernelEntropyBits (meanOutput W μ) ≠ ⊤)
    (n : ℕ) (P : Matrix (Fin n → I) (Fin n → I) ℂ) (hP : IsOrthProjector P) :
    (∀ a b, Integrable (fun x => productPureCQChannel W n x a *
          star (productPureCQChannel W n x b)) (Measure.pi fun _ : Fin n => μ) ∧
      ∫ x, productPureCQChannel W n x a * star (productPureCQChannel W n x b) ∂(Measure.pi fun _ : Fin n => μ) =
        HolevoCQ.tensorPowMat (meanOutput W μ) n a b) ∧
    (Integrable (fun x => realFockTracePair (idArr (Fin n → I))
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x)))) (Measure.pi fun _ : Fin n => μ) ∧
      Integrable (fun x => realFockTracePair P
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x)))) (Measure.pi fun _ : Fin n => μ) ∧
      Integrable (fun x => realFockTracePair (idArr (Fin n → I) - P)
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x)))) (Measure.pi fun _ : Fin n => μ) ∧
      Integrable (fun x => vecNormSq (arrApply P (productPureCQChannel W n x))) (Measure.pi fun _ : Fin n => μ)) ∧
    1 = ∫ x, realFockTracePair (idArr (Fin n → I))
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x))) ∂(Measure.pi fun _ : Fin n => μ) ∧
    ∫ x, realFockTracePair (idArr (Fin n → I))
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x))) ∂(Measure.pi fun _ : Fin n => μ) =
      (∫ x, realFockTracePair P
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x))) ∂(Measure.pi fun _ : Fin n => μ)) +
      ∫ x, realFockTracePair (idArr (Fin n → I) - P)
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x))) ∂(Measure.pi fun _ : Fin n => μ) ∧
    ∫ x, realFockTracePair P
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x))) ∂(Measure.pi fun _ : Fin n => μ) =
      ∫ x, vecNormSq (arrApply P (productPureCQChannel W n x)) ∂(Measure.pi fun _ : Fin n => μ) ∧
    ∫ x, realFockTracePair (idArr (Fin n → I) - P)
        (Matrix.vecMulVec (productPureCQChannel W n x) (star (productPureCQChannel W n x))) ∂(Measure.pi fun _ : Fin n => μ) =
      realFockTracePair (idArr (Fin n → I) - P) (HolevoCQ.tensorPowMat (meanOutput W μ) n) ∧
    1 = (∫ x, vecNormSq (arrApply P (productPureCQChannel W n x)) ∂(Measure.pi fun _ : Fin n => μ)) +
      realFockTracePair (idArr (Fin n → I) - P) (HolevoCQ.tensorPowMat (meanOutput W μ) n) := by sorry

end SeqHolevo
