-- Prove2me | Theorems.Thm_SeqHolevo_theorem_1
-- name    : SeqHolevo.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:02:16.629551+00:00
-- url     : https://prove2.me/theorems/d02ddfff-38ae-4909-b440-df03c9cc0420
-- title:
--   Theorem 1 — sequential decoding achieves the Holevo rate $H(\rho)$ of a pure-state channel
-- statement:
--   Let $x\mapsto|\varphi_x\rangle$ be a classical-quantum channel with pure output states, let $p_X$ be a distribution on its inputs (discrete or continuous), and let
--
--   $$\rho=\sum_xp_X(x)\,|\varphi_x\rangle\langle\varphi_x|\qquad(\text{an integral for continuous inputs})$$
--
--   have finite von Neumann entropy $H(\rho)$ (bits). Then every rate $R<H(\rho)$ is achievable with the **sequential decoder**: for every $\varepsilon>0$ and all sufficiently large $n$ there is a code of $M\ge2^{nR}$ codewords in $X^n$ such that the receiver who asks "is it codeword 1?", "is it codeword 2?", … — each question the binary projective measurement $\{|\varphi_{x^n(i)}\rangle\langle\varphi_{x^n(i)}|,\ I-|\varphi_{x^n(i)}\rangle\langle\varphi_{x^n(i)}|\}$ — and stops at the first "yes", decodes every message correctly with probability at least $1-\varepsilon$.
--
--   The Holevo rate is thus attained by an explicit receiver, a sequence of rank-one projective tests, rather than an abstract collective measurement.
--
--   The channel $x\mapsto|\varphi_x\rangle$ is a family of unit vectors $W(x)\in\ell^2(I)$ for an arbitrary index set $I$ (so the output Hilbert space is arbitrary, infinite-dimensional allowed), the input space $X$ is any measurable space (discrete or continuous), $p_X$ is any probability measure $\mu$ on $X$ for which the matrix entries of $x\mapsto|\varphi_x\rangle\langle\varphi_x|$ are measurable, $\rho=\int|\varphi_x\rangle\langle\varphi_x|\,d\mu(x)$ (coefficientwise), and $H(\rho)<\infty$ (von Neumann entropy in bits).
--
--   Differences from the source:
--   - encoding: a distribution p_X(x), x discrete or continuous; ρ ≡ Σ_x p_X(x)|φ_x⟩⟨φ_x| → any probability measure μ on any measurable space X with measurable matrix entries of x ↦ |φ_x⟩⟨φ_x|; ρ = meanOutput W μ (coefficientwise integral); reason: a sum over a discrete X is the integral against a discrete μ; measurability of the entries is what makes ρ and the random codebook defined, and is automatic for a discrete X
--   - encoding: pure states |φ_x⟩ of a Hilbert space; |φ_{xⁿ}⟩ = |φ_{x_1}⟩ ⊗ ⋯ ⊗ |φ_{x_n}⟩ → unit coefficient vectors W x on ℓ²(I) for an arbitrary I : Type; productPureCQChannel W n on the product basis Fin n → I; reason: every Hilbert space has an orthonormal basis, and the product basis indexes the completed tensor product; no finiteness or countability is imposed
--   - reading: H(ρ) used as a real number (rate "H(ρ) bits per channel use") → hypothesis kernelEntropyBits (meanOutput W μ) ≠ ⊤; reason: the rate H(ρ) and the proof's |H̄(xⁿ) − H(X)| ≤ δ require a finite entropy
--   - reading: "the rate H(ρ) … is achievable" → every real R < H(ρ) is achievable (SeqAchievable): M ≥ 2^{nR} codewords with maximal error ≤ ε for all large n; reason: the standard notion of the paper's ref. [4]; the proof uses |𝓜| = 2^{n[H(ρ)−2δ]} and ends with expurgation, which gives maximal error, the stronger of the two error criteria
--   - encoding: messages 1, …, 2^{nR}; the decoder tests codewords 1, 2, … in order → Fin M, 0-based; the decoder (seqError) is the vector recursion of the code's own codewords; reason: the same decoder: |⟨Φ_m|Π̂_{m−1}⋯Π̂_1|Φ_m⟩|² equals the printed trace because φ is a rank-one projector
--   - encoding: bits → logTwo / kernelEntropyBits in bits, 2^{nR} a real power; reason: as printed
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Theorem 1, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
import Definitions.Def_SeqHolevo_SeqAchievable

open MeasureTheory
open QAlgorithms.Papers.Independent.Intakenext100.P76 (IsUnitCoefficientVector meanOutput kernelEntropyBits)
open scoped ENNReal

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Theorem 1, p.2 (PDF page; the paper prints no page numbers): "Let `x → |φ_x⟩` be a
classical-quantum channel and let `ρ ≡ Σ_x p_X(x) |φ_x⟩⟨φ_x|` for some distribution `p_X(x)`.
Then the rate `H(ρ)` bits per channel use is achievable for communication over this channel by
having the receiver employ a sequential decoding strategy."

Every rate `R < H(ρ)` is achievable with the sequential decoder, under the maximal error
criterion (`SeqAchievable`).

**Formalization Note.** The channel `x ↦ |φ_x⟩` is `W : X → I → ℂ`, a unit coefficient vector on ℓ²(I) for every input,
with `X` any measurable space (discrete or continuous) and `I` any index type (no finiteness or
countability: ℓ²(I) is an arbitrary Hilbert space). `p_X` is any probability measure `μ` on `X`;
the only measurability assumed is that of the matrix entries of `x ↦ |φ_x⟩⟨φ_x|` (the published
`Intakenext100.P76` convention; automatic for a discrete `X`), and `ρ` is the coefficientwise
integral `meanOutput W μ`. `H(ρ)` is the published `kernelEntropyBits` (bits, `+∞` allowed, `⊤`
if `ρ` has no spectral law); `hfin` is the reading that `H(ρ)` is a real number, as the paper uses
it. "The rate `H(ρ)` is achievable" is read (R1) as: every
`R < H(ρ)` is achievable, with maximal error over messages; the decoder is the sequential decoder
of the code's own codewords. -/
theorem theorem_1 {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {I : Type}
    (W : X → I → ℂ) (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (hfin : kernelEntropyBits (meanOutput W μ) ≠ ⊤)
    (R : ℝ) (hR : R < (kernelEntropyBits (meanOutput W μ)).toReal) :
    SeqAchievable W R := by sorry

end SeqHolevo
