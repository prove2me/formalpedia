-- Prove2me | Theorems.Thm_SepMeasures_eq_8
-- name    : SepMeasures.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:10:46.636294+00:00
-- url     : https://prove2.me/theorems/b1a2fea2-bad5-432a-869e-e428430fa9c2
-- title:
--   Eq. (8) — for every line $K$: $\Phi_K\le1$, i.e. $\sum_{i=1}^3 I_i(K)\ge D(K)$
-- statement:
--   This is the separation-probability inequality inside the proof of Theorem 3.3. Let $\mu,\nu$ be probability measures on $\mathbb R^2$ and $H_1,H_2,H_3$ lines satisfying the bisection identities of p.20,
--   $$\mathbb E_\mu[\sigma_{H_1}]=\mathbb E_\mu[\sigma_{H_2}]=\mathbb E_\mu[\sigma_{H_1}\sigma_{H_3}]=0,\qquad \mathbb E_\nu[\sigma_{H_1}]=\mathbb E_\nu[\sigma_{H_3}]=\mathbb E_\nu[\sigma_{H_1}\sigma_{H_2}]=0 .$$
--   Let $K$ be a line, with $H_1,H_2,H_3,K$ all of $\mu$- and $\nu$-measure $0$. Put $p_0=\mathbb E_\mu[\sigma_K]$, $q_0=\mathbb E_\nu[\sigma_K]$, $p_i=\mathbb E_\mu[\sigma_K\sigma_{H_i}]$, $q_i=\mathbb E_\nu[\sigma_K\sigma_{H_i}]$ and $\Phi_K=p_0q_0-\sum_{i=1}^3p_iq_i$. Let $D(K)$ be the probability that $K$ strictly separates independent $X\sim\mu$, $Y\sim\nu$, and $I_i(K)$ the probability that both $K$ and $H_i$ do. Then both sides of the equivalence (8) hold:
--   $$\Phi_K\le1\qquad\text{and}\qquad \sum_{i=1}^3 I_i(K)\ \ge\ D(K).$$
--
--   Integrating the second inequality over all lines against Pinelis's representation of the norm gives $C(H_1)+C(H_2)+C(H_3)\ge L$, hence Theorem 3.3.
--
--   Differences from the source:
--   - generalization: µ, ν absolutely continuous (𝒫²_bc), so every line is null → only the four lines H₁, H₂, H₃, K are assumed µ- and ν-null; reason: the proof uses only these null sets (through Lemmas 2.4, 2.5 and Claims 3.4, 3.5); absolutely continuous measures satisfy them
--   - generalization: H₁, H₂, H₃ chosen by Lemma 2.3 to bisect (µ, ν), (µ, σ_{H₁}ν), (ν, σ_{H₁}µ) → any lines with the six expectation identities of p.20; reason: the chosen lines satisfy these identities and the proof uses only them
--   - encoding: (8): Φ_K ≤ 1 ⟺ Σᵢ Iᵢ(K) − D(K) ≥ 0, which the proof establishes for every line K → the conjunction Φ_K ≤ 1 ∧ D(K) ≤ I₁(K) + I₂(K) + I₃(K); reason: the paper proves Φ_K ≤ 1 and uses the equivalent inequality Σ Iᵢ ≥ D; stating both sides keeps all of (8)
--   - encoding: independent X ∼ µ, Y ∼ ν; Pr[·]; E_µ[σ_K] → the product measure µ.prod ν and its real-valued measure (µ.prod ν).real; Bochner integrals ∫ σ_K dµ; reason: σ_K is bounded and measurable, so the integrals are the expectations; the product measure is the law of an independent pair
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Eq. (8), p.22 (proved pp.22–25), in the proof of Theorem 3.3 (context pp.20–21)

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Eq. (8), p.22 (proved pp.22–25), in the context of
the proof of Theorem 3.3 (pp.20–21). Let `μ, ν` be probability measures on `ℝ²` and
`H₁, H₂, H₃` lines with the bisection identities of p.20,
`E_μ[σ_{H₁}] = E_μ[σ_{H₂}] = E_μ[σ_{H₁}σ_{H₃}] = 0` and
`E_ν[σ_{H₁}] = E_ν[σ_{H₃}] = E_ν[σ_{H₁}σ_{H₂}] = 0`.
For every line `K`, with `p₀ = E_μ[σ_K]`, `q₀ = E_ν[σ_K]`, `pᵢ = E_μ[σ_K σ_{Hᵢ}]`,
`qᵢ = E_ν[σ_K σ_{Hᵢ}]` and `Φ_K = p₀q₀ − Σᵢ pᵢqᵢ`, both sides of (8) hold:
`Φ_K ≤ 1` and `Σᵢ Iᵢ(K) ≥ D(K)`, where `D(K)` is the probability that `K` strictly separates
independent `X ∼ μ`, `Y ∼ ν` and `Iᵢ(K)` the probability that both `K` and `Hᵢ` do.

**Formalization Note.** The proof's context is written out as hypotheses. All four lines are
assumed `μ`- and `ν`-null (in the paper `μ, ν` are absolutely continuous, so every line is
null). Independence is the product measure `μ.prod ν`. -/
theorem eq_8 (μ ν : Measure (E 2)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H₁ H₂ H₃ K : Hyp 2)
    (hμ₁ : μ H₁.set = 0) (hμ₂ : μ H₂.set = 0) (hμ₃ : μ H₃.set = 0) (hμK : μ K.set = 0)
    (hν₁ : ν H₁.set = 0) (hν₂ : ν H₂.set = 0) (hν₃ : ν H₃.set = 0) (hνK : ν K.set = 0)
    (bμ₁ : ∫ x, H₁.sign x ∂μ = 0) (bμ₂ : ∫ x, H₂.sign x ∂μ = 0)
    (bμ₁₃ : ∫ x, H₁.sign x * H₃.sign x ∂μ = 0)
    (bν₁ : ∫ y, H₁.sign y ∂ν = 0) (bν₃ : ∫ y, H₃.sign y ∂ν = 0)
    (bν₁₂ : ∫ y, H₁.sign y * H₂.sign y ∂ν = 0) :
    (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)
        - ((∫ x, K.sign x * H₁.sign x ∂μ) * (∫ y, K.sign y * H₁.sign y ∂ν)
          + (∫ x, K.sign x * H₂.sign x ∂μ) * (∫ y, K.sign y * H₂.sign y ∂ν)
          + (∫ x, K.sign x * H₃.sign x ∂μ) * (∫ y, K.sign y * H₃.sign y ∂ν)) ≤ 1 ∧
    (μ.prod ν).real (Sep K) ≤
      (μ.prod ν).real (Sep K ∩ Sep H₁) + (μ.prod ν).real (Sep K ∩ Sep H₂)
        + (μ.prod ν).real (Sep K ∩ Sep H₃) := by sorry

end SepMeasures
