-- Prove2me | Theorems.Thm_PreservePast_lemma_2
-- name    : PreservePast.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:20.084201+00:00
-- url     : https://prove2.me/theorems/349f999a-304a-4e90-9acc-5c60e8cc85b7
-- title:
--   Lemma 2 — shared-response exponents for Haar frames
-- statement:
--   Let $\mu$ be the Haar law of an ordered orthonormal $t$-frame $U\in\mathbb R^{D\times t}$ ($D\ge t$), and consider the quadratic score $g_U(C)=2\langle U,C\rangle-\|C\|_F^2$ over candidates $C\in\mathbb R^{D\times t}$, with domain $\mathcal T$ the orthonormal frames. Then $V(U)=t$ and $V(U)-g_U(C)=\|U-C\|_F^2$ for every frame $U$, and:
--
--   1. (constant correlation) with $\psi(z)=z-1-\ln z$, if $0<\eta<1$ and $z=n\eta(D-t+1)/D>1$, then
--   $$
--   \mathcal H_n(t(1-\eta);\mu)\ge\frac{Dt}{2n}\psi(z);
--   $$
--   2. in particular, if $d$ satisfies $D-t+1\ge d/2$ and $D\le d$, the tuple order $n=\lceil8/\eta\rceil$ gives $\mathcal H_n(t(1-\eta);\mu)\ge dt\eta/16$;
--   3. (fine accuracy) if $1\le t\le D/2$ and $0<e<1/(2\sqrt2)$, then
--   $$
--   \mathcal H_2(te^2;\mu)\ge\frac{t(D-t)}4\ln\frac1{2\sqrt2e}-\frac t2\ln2 .
--   $$
--
--   These two exponents drive the covariance and rank-dependent lower bounds of Theorem 4.
--
--   **Formalization Note** Frames and candidates are $t$-tuples of columns in $\mathbb R^D$, $\langle U,C\rangle=\sum_j\langle U_j,C_j\rangle$; $\mathcal H_n$ is the extended-real source exponent of (2).
--
--   Differences from the source:
--   - encoding: µ the Haar law of t-frames → any probability law concentrated on orthonormal frames and invariant under all orthogonal maps; reason: this characterizes the Haar law, which exists (verification file); same instances
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3, p.6 (PDF p.8), Lemma 2, (8)–(10)

import Mathlib
import Definitions.Def_PreservePast_IsHaarFrame
import Definitions.Def_PreservePast_sourceExp

open MeasureTheory

namespace PreservePast

/-- **Lemma 2 (shared-response exponents for Haar frames).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3, p.6 (PDF p.8): "Let µ be the
Haar law, namely the uniform rotation-invariant law, of an ordered orthonormal t-frame U ∈ ℝ^{D×t}
(D ≥ t); the columns of U are t orthonormal vectors. For the quadratic score
g_U(C) = 2⟨U, C⟩ − ‖C‖²_F over candidate approximations C ∈ ℝ^{D×t} to U, we have V(U) = t and
V(U) − g_U(C) = ‖U − C‖²_F. 1. Constant-correlation regime: Put ψ(z) = z − 1 − ln z. If 0 < η < 1
and z = nη(D − t + 1)/D > 1, then 𝓗_n(t(1 − η); µ) ≥ (Dt/(2n))ψ(z). (8) In particular, for an
ambient dimension d with D − t + 1 ≥ d/2 and D ≤ d, choosing tuple order n = ⌈8/η⌉ gives
𝓗_n(t(1 − η); µ) ≥ dtη/16 (9). 2. Fine-accuracy regime: If 1 ≤ t ≤ D/2 and 0 < e < 1/(2√2), the
two-history exponent at squared Frobenius error te² satisfies
𝓗₂(te²; µ) ≥ (t(D − t)/4) ln(1/(2√2e)) − (t/2) ln 2. (10)"

The history space and the action space are `D × t` matrices, written as `t`-tuples of columns in
`ℝ^D`; the domain `𝒯` is the set of orthonormal frames; `𝓗_n` is `sourceExp` (in nats).

**Formalization Note.** `⟨U, C⟩ = Σ_j ⟨U_j, C_j⟩` and `‖C‖²_F = Σ_j ‖C_j‖²` over the columns.
The conclusions are in `EReal`. -/
theorem lemma_2 (D t : ℕ) (hDt : t ≤ D) (μ : Measure (Fin t → EuclideanSpace ℝ (Fin D)))
    (hμ : IsHaarFrame D t μ) :
    let g : (Fin t → EuclideanSpace ℝ (Fin D)) → (Fin t → EuclideanSpace ℝ (Fin D)) → ℝ :=
      fun U C => 2 * ∑ j, inner ℝ (U j) (C j) - ∑ j, ‖C j‖ ^ 2
    let 𝒯 : Set (Fin t → EuclideanSpace ℝ (Fin D)) := {U | Orthonormal ℝ U}
    (∀ U ∈ 𝒯, optVal g U = t ∧ ∀ C, optVal g U - g U C = ∑ j, ‖U j - C j‖ ^ 2) ∧
    (∀ (n : ℕ) (η : ℝ), 0 < η → η < 1 → 1 < n * η * ((D : ℝ) - t + 1) / D →
      (((D * t / (2 * n) : ℝ) * (n * η * ((D : ℝ) - t + 1) / D - 1 -
          Real.log (n * η * ((D : ℝ) - t + 1) / D)) : ℝ) : EReal) ≤
        sourceExp g 𝒯 μ n (t * (1 - η))) ∧
    (∀ (d : ℕ) (η : ℝ), 0 < η → η < 1 → (d : ℝ) / 2 ≤ (D : ℝ) - t + 1 → D ≤ d →
      ((d * t * η / 16 : ℝ) : EReal) ≤ sourceExp g 𝒯 μ ⌈8 / η⌉₊ (t * (1 - η))) ∧
    (1 ≤ t → 2 * t ≤ D → ∀ e : ℝ, 0 < e → e < 1 / (2 * Real.sqrt 2) →
      ((t * ((D : ℝ) - t) / 4 * Real.log (1 / (2 * Real.sqrt 2 * e)) - t / 2 * Real.log 2 : ℝ) :
          EReal) ≤ sourceExp g 𝒯 μ 2 (t * e ^ 2)) := by sorry

end PreservePast
