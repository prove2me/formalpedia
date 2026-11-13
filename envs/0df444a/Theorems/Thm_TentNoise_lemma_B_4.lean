-- Prove2me | Theorems.Thm_TentNoise_lemma_B_4
-- name    : TentNoise.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:31.972585+00:00
-- url     : https://prove2.me/theorems/920a9d76-f9df-49c0-b527-b0971417ba64
-- title:
--   Lemma B.4 — the linear observable: $R_f\varphi=0$, $R_u\varphi=A$, $\int_0^1A\cos(\pi N y)\,dy=-b/4$
-- statement:
--   For the perturbation of Lemma B.3 ($N\ge1$, $0<b\le1/32$) let $\varphi(x)=x-\tfrac12$. Then for $y\in[0,1]$
--
--   $$
--   (R_f\varphi)(y)=0,\qquad A(y):=(R_u\varphi)(y)=u(y)+(y-1)u'(y),
--   $$
--
--   and
--
--   $$
--   \int_0^1A(y)\cos(\pi Ny)\,dy=-\frac b4,\qquad \|A\|_1\le\frac{b}{\pi N}+\frac b2\le b .
--   $$
--
--   The true reverse dynamics leave the centered state unbiased, while the fitted ones produce a conditional mean with a frequency-$N$ component of size $b$.
--
--   **Formalization Note** $(R\varphi)(y)=\int\varphi\,dR(y,\cdot)$ with $R_f$ the tent map's reverse kernel and $R_u$ that of Lemma B.3; $\|A\|_1=\int_0^1|A|$.
--
--   Differences from the source:
--   - encoding: (Rφ)(y) and ‖A‖_1 → ∫ (x − 1/2) d R(y, ·) for y ∈ [0,1]; ∫_0^1 |A(y)| dy; reason: direct transcription
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.4, p.27 (PDF p.27), eqs. (62)–(63)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_revTent
import Definitions.Def_TentNoise_revKernelFit
import Definitions.Def_TentNoise_condMeanA

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma B.4 (The linear observable and its conditional mean)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.4, p.27,
eqs. (62)–(63)): for the perturbation of Lemma B.3 and `φ(x) = x − 1/2`,
`(R_f φ)(y) = 0`, `A(y) := (R_u φ)(y) = u(y) + (y − 1)u′(y)`, and
`∫₀¹ A(y) cos(πNy) dy = −b/4`, `‖A‖₁ ≤ b/(πN) + b/2 ≤ b`.

**Formalization Note** `N ≥ 1`, `0 < b ≤ 1/32` (Lemma B.3's hypotheses). `R_f = revTent` (eq. (3)),
`R_u = revKernelFit N b` (eq. (61)); `(Rφ)(y) = ∫ φ dR(y, ·)` for `y ∈ [0, 1]`. `‖A‖₁ = ∫₀¹ |A|`. -/
theorem lemma_B_4 (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 32) :
    (∀ y ∈ Icc (0 : ℝ) 1, ∫ x, (x - 1 / 2) ∂(revTent y) = 0) ∧
    (∀ y ∈ Icc (0 : ℝ) 1, ∫ x, (x - 1 / 2) ∂(revKernelFit N b y) = condMeanA N b y) ∧
    ∫ y in (0 : ℝ)..1, condMeanA N b y * Real.cos (Real.pi * N * y) = -(b / 4) ∧
    ∫ y in (0 : ℝ)..1, |condMeanA N b y| ≤ b / (Real.pi * N) + b / 2 ∧
    b / (Real.pi * N) + b / 2 ≤ b := by sorry

end TentNoise
