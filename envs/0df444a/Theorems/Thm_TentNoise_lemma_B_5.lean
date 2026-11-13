-- Prove2me | Theorems.Thm_TentNoise_lemma_B_5
-- name    : TentNoise.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:24.488796+00:00
-- url     : https://prove2.me/theorems/10559ee3-c734-4aa0-a4b3-a926ad72ee7e
-- title:
--   Lemma B.5 — reverse kernel of the fitted noisy chain and the cosine identities $H_\sigma\cos(\pi n\cdot)$, $\mathsf K_\sigma^k\psi$
-- statement:
--   Take $N=2^k$, $m=k+1$, $\psi(x)=\cos(\pi x)$, $\mathsf K_\sigma v=(H_\sigma v)\circ f$, and let $g$ be the fitted map of Lemma B.3 ($0<b\le1/32$), $\sigma\ge0$. For the stationary fitted noisy chain $Y_0\sim\mu$, $Y_1\sim H_\sigma(g(Y_0),\cdot)$, the reverse kernel and the centered conditional mean are
--
--   $$
--   R_{g,\sigma}(y,dx)=\int_0^1R_u(z,dx)\,H_\sigma(y,dz),\qquad \mathbb E[\varphi(Y_0)\mid Y_1=y]=(H_\sigma A)(y).
--   $$
--
--   Moreover, for every integer $n\ge0$,
--
--   $$
--   H_\sigma\cos(\pi n\,\cdot)(y)=e^{-\pi^2n^2\sigma^2/2}\cos(\pi ny),\qquad \mathsf K_\sigma^k\psi(y)=e^{-\pi^2\sigma^2(N^2-1)/6}\cos(\pi Ny).
--   $$
--
--   These identities include $\sigma=0$ and $k=0$. Also, $H_\sigma$ is self-adjoint on $L^2(\mu)$, contracts $L^1(\mu)$, and does not increase Lipschitz constants.
--
--   The true noisy dynamics double frequencies and damp amplitudes in a computable way; this lets a low-frequency observable at a later time detect the frequency-$N$ oscillation of $A$.
--
--   **Formalization Note** The reverse kernel is stated as the identity of joint laws $\mathrm{law}(Y_1,Y_0)=\mu\otimes R_{g,\sigma}$, and the conditional mean through its defining property $\mathbb E[\varphi(Y_0)w(Y_1)]=\int(H_\sigma A)\,w\,d\mu$ for every bounded Borel $w$. The cosine identities and the Lipschitz property are for $y\in[0,1]$; self-adjointness is $\int(H_\sigma v)w\,d\mu=\int v\,(H_\sigma w)\,d\mu$ for $v,w\in L^2(\mu)$; the $L^1$ contraction is $\int|H_\sigma v|\,d\mu\le\int|v|\,d\mu$ for $v\in L^1(\mu)$. $g$ is Borel on $\mathbb R$.
--
--   Differences from the source:
--   - encoding: the fitted map g of Lemma B.3 with N = 2^k ('From now on take N = 2^k', p.28), a map [0,1] → [0,1] → any g : ℝ → ℝ, measurable, with IsFitMap (2^k) b g (g ∘ h_0 = g ∘ h_1 = id on [0,1]) and 0 < b ≤ 1/32; reason: IsFitMap pins g down on [0,1] (Lemma B.3) and gives g([0,1]) = [0,1]; values of g off [0,1] are never visited; the paper's g extends to a Borel map of ℝ
--   - encoding: reverse kernel R_{g,σ} (64) and conditional expectation E[φ(Y_0) | Y_1 = y] (65) → law(Y_1, Y_0) = µ ⊗ (R_u ∘ₖ H_σ); E[φ(Y_0) w(Y_1)] = ∫ (H_σ A) w dµ for every bounded Borel w; reason: the a.e.-faithful content of a conditional law and of a conditional expectation
--   - encoding: H_σ self-adjoint on L²(µ), contracts L¹(µ), does not increase Lipschitz constants → ∫(H_σv)w dµ = ∫v(H_σw) dµ for v, w ∈ L²(µ); ∫|H_σv| dµ ≤ ∫|v| dµ for v ∈ L¹(µ) (lower integrals); LipschitzOnWith K v [0,1] → LipschitzOnWith K (H_σv) [0,1]; reason: direct transcription of the three operator properties on the state space [0,1]
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.5, pp.28–29 (PDF pp.28–29), eqs. (64)–(67)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_H
import Definitions.Def_TentNoise_unifI
import Definitions.Def_TentNoise_IsFitMap
import Definitions.Def_TentNoise_revKernelFit
import Definitions.Def_TentNoise_condMeanA

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma B.5** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.5, pp.28–29, eqs. (64)–(67)). With `N = 2^k`, `m = k + 1`,
`ψ(x) = cos(πx)`, `𝖪_σ v = (H_σ v) ∘ f`: the reverse kernel of the fitted noisy chain and its centered
conditional mean are `R_{g,σ}(y, dx) = ∫₀¹ R_u(z, dx) H_σ(y, dz)` and
`E[φ(Y₀) | Y₁ = y] = (H_σ A)(y)`; for every integer `n ≥ 0`,
`H_σ cos(πny) = e^{−π²n²σ²/2} cos(πny)` and `𝖪_σ^k ψ(y) = e^{−π²σ²(N²−1)/6} cos(πNy)`; these include
`σ = 0` and `k = 0`. Also `H_σ` is self-adjoint on `L²(µ)`, contracts `L¹(µ)`, and does not increase
Lipschitz constants.

**Formalization Note** `g` is Lemma B.3's map (`IsFitMap (2^k) b g`, `0 < b ≤ 1/32`), Borel on `ℝ`.
The stationary fitted chain is `Y₀ ∼ µ`, `Y₁ ∼ L_σ(Y₀, ·)`, with joint law `µ ⊗ L_σ`. (64) is the
identity of joint laws `law(Y₁, Y₀) = µ ⊗ R_{g,σ}`. (65) is the defining property of the conditional
expectation: `E[φ(Y₀) w(Y₁)] = ∫ (H_σA) w dµ` for every bounded Borel `w`. `(H_σ v)(y) = ∫ v dH_σ(y, ·)`.
(66), (67) and the Lipschitz property are stated for `y ∈ [0, 1]`; self-adjointness for `v, w ∈ L²(µ)`;
the `L¹` contraction for `v ∈ L¹(µ)`. -/
theorem lemma_B_5 (k : ℕ) (b : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 32) (g : ℝ → ℝ) (hg : Measurable g)
    (hfit : IsFitMap (2 ^ k) b g) (σ : ℝ) (hσ : 0 ≤ σ) :
    (unifI ⊗ₘ (H σ).comap g hg).map Prod.swap = unifI ⊗ₘ (revKernelFit (2 ^ k) b ∘ₖ H σ) ∧
    (∀ w : ℝ → ℝ, Measurable w → (∃ C : ℝ, ∀ y, |w y| ≤ C) →
      ∫ p, (p.1 - 1 / 2) * w p.2 ∂(unifI ⊗ₘ (H σ).comap g hg) =
        ∫ y, (∫ z, condMeanA (2 ^ k) b z ∂(H σ y)) * w y ∂unifI) ∧
    (∀ n : ℕ, ∀ y ∈ Icc (0 : ℝ) 1,
      ∫ z, Real.cos (Real.pi * n * z) ∂(H σ y) =
        Real.exp (-(Real.pi ^ 2 * n ^ 2 * σ ^ 2) / 2) * Real.cos (Real.pi * n * y)) ∧
    (∀ y ∈ Icc (0 : ℝ) 1,
      (fun v : ℝ → ℝ => fun x => ∫ z, v z ∂(H σ (tentMap 2 x)))^[k]
          (fun x => Real.cos (Real.pi * x)) y =
        Real.exp (-(Real.pi ^ 2 * σ ^ 2 * (((2 : ℝ) ^ k) ^ 2 - 1)) / 6) *
          Real.cos (Real.pi * (2 : ℝ) ^ k * y)) ∧
    (∀ v w : ℝ → ℝ, MemLp v 2 unifI → MemLp w 2 unifI →
      ∫ y, (∫ z, v z ∂(H σ y)) * w y ∂unifI = ∫ y, v y * (∫ z, w z ∂(H σ y)) ∂unifI) ∧
    (∀ v : ℝ → ℝ, Integrable v unifI →
      ∫⁻ y, ENNReal.ofReal |∫ z, v z ∂(H σ y)| ∂unifI ≤ ∫⁻ y, ENNReal.ofReal |v y| ∂unifI) ∧
    (∀ (v : ℝ → ℝ) (K : ℝ≥0), LipschitzOnWith K v (Icc 0 1) →
      LipschitzOnWith K (fun y => ∫ z, v z ∂(H σ y)) (Icc 0 1)) := by sorry

end TentNoise
