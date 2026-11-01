-- Prove2me | Theorems.Thm_SeqHolevo_eps_prime_bound
-- name    : SeqHolevo.eps_prime_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:02:41.436549+00:00
-- url     : https://prove2.me/theorems/c87e11f7-3816-4929-9331-84773047e132
-- title:
--   Appendix B, p.7 — the overall bound $\varepsilon'$ on the expected error
-- statement:
--   For every $\delta>0$ and $\varepsilon>0$ there is $N$ such that for every $n\ge N$ and every number of messages $|\mathcal M|=M\ge1$, the expected error (8) of the sequential decoder of a random codebook ($M$ codewords drawn i.i.d. from $p_{X^n}$, uniform message) satisfies
--
--   $$\mathbb E\,(\text{error})\le\varepsilon'\equiv\varepsilon+2\sqrt\varepsilon+2\sqrt{2\sqrt\varepsilon+2^{-n[H(\rho)-\delta]}\,|\mathcal M|},$$
--
--   and the error is an integrable function of the codebook. Choosing $|\mathcal M|=2^{n[H(\rho)-2\delta]}$ makes $\varepsilon'$ arbitrarily small, which is the random-coding half of Theorem 1.
--
--   The channel $x\mapsto|\varphi_x\rangle$ is a family of unit vectors $W(x)\in\ell^2(I)$ for an arbitrary index set $I$ (so the output Hilbert space is arbitrary, infinite-dimensional allowed), the input space $X$ is any measurable space (discrete or continuous), $p_X$ is any probability measure $\mu$ on $X$ for which the matrix entries of $x\mapsto|\varphi_x\rangle\langle\varphi_x|$ are measurable, $\rho=\int|\varphi_x\rangle\langle\varphi_x|\,d\mu(x)$ (coefficientwise), and $H(\rho)<\infty$ (von Neumann entropy in bits).
--
--   Differences from the source:
--   - encoding: a distribution p_X(x), x discrete or continuous; ρ ≡ Σ_x p_X(x)|φ_x⟩⟨φ_x| → any probability measure μ on any measurable space X with measurable matrix entries of x ↦ |φ_x⟩⟨φ_x|; ρ = meanOutput W μ (coefficientwise integral); reason: a sum over a discrete X is the integral against a discrete μ; measurability of the entries is what makes ρ and the random codebook defined, and is automatic for a discrete X
--   - encoding: pure states |φ_x⟩ of a Hilbert space; |φ_{xⁿ}⟩ = |φ_{x_1}⟩ ⊗ ⋯ ⊗ |φ_{x_n}⟩ → unit coefficient vectors W x on ℓ²(I) for an arbitrary I : Type; productPureCQChannel W n on the product basis Fin n → I; reason: every Hilbert space has an orthonormal basis, and the product basis indexes the completed tensor product; no finiteness or countability is imposed
--   - reading: H(ρ) used as a real number (rate "H(ρ) bits per channel use") → hypothesis kernelEntropyBits (meanOutput W μ) ≠ ⊤; reason: the rate H(ρ) and the proof's |H̄(xⁿ) − H(X)| ≤ δ require a finite entropy
--   - encoding: expectation over the random codebook (codewords i.i.d. p_{Xⁿ}) and a uniformly random message M ∈ {1, …, |𝓜|} → Bochner integral against codebookLaw μ n M = (μ^{⊗n})^{⊗M} of the message average (1/M) Σ_m, with M ≥ 1, each asserted with integrability; reason: the same expectation; the integrability conjuncts exclude Lean's default value 0 for a non-integrable function
--   - encoding: messages 1, …, |𝓜| and tests Π̂_1, …, Π̂_{M−1} before message M → Fin M, 0-based: message m is preceded by the tests of codewords 0, …, m − 1; reason: relabelling only
--   - reading: "the overall upper bound on the error probability … is ε′", assembled from (11) (n sufficiently large) and the two term bounds → ∀ δ > 0, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ M ≥ 1: E (8) ≤ ε′; reason: N comes from (9)–(10) and depends on δ, ε and the channel; the term bounds hold for every M
--   - encoding: H(ρ) → (kernelEntropyBits ρ).toReal, finite by hfin; reason: the published entropy in bits
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, p.7, unnumbered display defining ε′

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
import Definitions.Def_SeqHolevo_codeAvgError

open MeasureTheory
open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector coefficientInner meanOutput kernelEntropyBits productPureCQChannel)
open QAlgorithms.Papers.Independent.Dependency50.P33 (traceSize)
open QAlgorithms.Papers.Independent.Next46.P32 (realFockTracePair)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.7 (PDF page; unnumbered display): "Thus, the overall upper bound on the
error probability with this sequential decoding strategy is
`ε′ ≡ ε + 2√ε + 2 √(2√ε + 2^{−n[H(ρ)−δ]} |𝓜|)`, which we can make arbitrarily small by choosing
`|𝓜| = 2^{n[H(ρ)−2δ]}` and `n` sufficiently large."

For every `δ > 0` and `ε > 0` there is `N` such that for every `n ≥ N` and every number of
messages `M ≥ 1`, the expected average error (8) of the sequential decoder of the random code
(codebook `(p_{Xⁿ})^{⊗M}`, uniform message) is at most `ε′`.

**Formalization Note.** The channel `x ↦ |φ_x⟩` is `W : X → I → ℂ` (unit coefficient vectors on ℓ²(I), any measurable
space `X`, any index type `I`), `p_X` is any probability measure `μ`, the matrix entries of
`x ↦ |φ_x⟩⟨φ_x|` are measurable, `ρ = meanOutput W μ`, and `hfin` says `H(ρ) < ∞` (published
`Intakenext100.P76` objects; see `theorem_1`). The random codebook `C : Fin M → Fin n → X` has the
law `codebookLaw μ n M = (p_{Xⁿ})^{⊗M}` and the message is uniform on `Fin M` (weights `1/M`,
`M ≥ 1`); `|φ_{Xⁿ(m)}⟩ = codeVecs W n C m`. Expectations are Bochner integrals asserted together
with integrability (no default-zero integral). Messages and tests are 0-based: the paper's
`Π̂_1, …, Π̂_{M−1}` before message `M` are Lean's tests `0, …, m−1` before message `m`. (8) is `E_C codeAvgError`. `H(ρ) = (kernelEntropyBits ρ).toReal`
(finite by `hfin`), `2^x` the real power. `N` depends on `δ`, `ε` and the channel, not on `M`. -/
theorem eps_prime_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {I : Type}
    (W : X → I → ℂ) (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (hfin : kernelEntropyBits (meanOutput W μ) ≠ ⊤) :
    ∀ δ > 0, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ M : ℕ, 0 < M →
      Integrable (fun C : Fin M → Fin n → X => codeAvgError W n C) (codebookLaw μ n M) ∧
      ∫ C, codeAvgError W n C ∂(codebookLaw μ n M) ≤
        ε + 2 * Real.sqrt ε + 2 * Real.sqrt (2 * Real.sqrt ε +
          (2 : ℝ) ^ (-((n : ℝ) * ((kernelEntropyBits (meanOutput W μ)).toReal - δ))) * M) := by sorry

end SeqHolevo
