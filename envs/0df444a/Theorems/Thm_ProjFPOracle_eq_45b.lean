-- Prove2me | Theorems.Thm_ProjFPOracle_eq_45b
-- name    : ProjFPOracle.eq_45b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:19.929225+00:00
-- url     : https://prove2.me/theorems/fdca3ee3-29e5-40b4-85ad-666ed82c9147
-- title:
--   Eq. (45b), p.27 (corrected: the sample size also controls the initialization bias and the stepsize lies in Lemma 5's stability range) — estimation error
-- statement:
--   There are universal constants $c_0,c>0$ such that the following holds. Let $\mathbb X$ be a real Hilbert space, $\mathbb S$ a subspace with orthonormal basis $\varphi_1,\dots,\varphi_d$ ($d\ge1$), $L$ a bounded operator with $I-L$ boundedly invertible, $b\in\mathbb X$, $M=\Phi_dL\Phi_d^*$ with $\kappa=\kappa(M)<1$, and $\bar v$ the projected fixed point. Let the observations be i.i.d., unbiased and satisfy Assumption 1(W) with $\sigma_L,\sigma_b>0$, let $v_0\in\mathbb S$ be fixed, and run the algorithm (24) with
--   $$
--   \eta=\frac1{c_0\sigma_L\sqrt{dn}},\qquad n_0=\lfloor n/2\rfloor .
--   $$
--   Suppose $n\ge2$ and
--
--   1. $n\ge\dfrac{c_0\sigma_L^2d}{(1-\kappa)^2}\log^2\Big(\dfrac{\|v_0-\bar v\|^2d}{1-\kappa}\Big)$ (the printed threshold);
--   2. $\eta<\dfrac{1-\kappa}{4\sigma_L^2d+2(1+|||L|||_{\mathbb X}^2)}$ (added);
--   3. $n\ge\dfrac{c_0\sigma_L^2d}{(1-\kappa)^2}\log^2\Big(e+\dfrac{\|v_0-\bar v\|^2(1-\kappa)\sigma_L\sqrt n}{\sqrt d\,(\|\bar v\|^2\sigma_L^2+\sigma_b^2)}\Big)$ (added).
--
--   Then
--   $$
--   \mathbb E\|\widehat v_n-\bar v\|^2\le c\,\frac{\operatorname{trace}\big((I-M)^{-1}\Sigma^*(I-M)^{-\top}\big)}{n}+c\,\frac{\sigma_L}{(1-\kappa)^3}\Big(\frac dn\Big)^{3/2}\big(\|\bar v\|^2\sigma_L^2+\sigma_b^2\big).
--   $$
--   This is the statistical half of Theorem 1: the averaged estimator attains the local complexity $\mathcal E_n(M,\Sigma^*)$ up to a constant, plus a term of order $n^{-3/2}$.
--
--   Hypotheses 2 and 3 are not on the page; without them the printed statement is false (see the corrections below).
--
--   Differences from the source:
--   - correction: sample-size threshold n ≥ (c₀σ_L²d/(1−κ)²) log²(‖v₀ − v̄‖²d/(1−κ)) only → additionally (iii) n ≥ (c₀σ_L²d/(1−κ)²) log²(e + ‖v₀ − v̄‖²(1−κ)σ_L√n/(√d(‖v̄‖²σ_L² + σ_b²))); reason: the printed bound is false: 𝕏 = 𝕊 = ℝ, L = L_i ≡ 0, b = b_i ≡ 0, v₀ = 1, σ_L = 1, σ_b = ε meets every printed assumption for every n ≥ 2 (threshold c₀ log²1 = 0); the left side is ≥ (1 − η)^{2n} > 0 independently of ε, the right side c(1 + 1/ω)ε²/n^{3/2} → 0 as ε → 0
--   - correction: stepsize η = 1/(c₀σ_L√(dn)) with no further condition → additionally (ii) η < (1−κ)/(4σ_L²d + 2(1 + |||L|||²_𝕏)); reason: the printed bound is false: 𝕏 = 𝕊 = ℝ, L = L_i ≡ m, b = b_i ≡ 0, σ_L = σ_b = 1, v₀ = 1, n = 2; as m → −∞ both thresholds tend to 0 while the left side (1 − η(1 − m))⁴ → ∞ and the right side → 0
--   - reading: Lemma/Theorem statement without the standing assumptions of §2.1 and §5.1 → hypotheses IsUnit (1 − L) and κ(M) < 1; reason: p.7 "We assume that the operator I − L has a bounded inverse"; p.28 "our assumption that κ(M) < 1"; the statements need both
--   - reading: "there are universal constants (c₀, c)" → ∃ c₀ > 0, ∃ c > 0 quantified before d, 𝕏, 𝕊, L, b, the law of the observations, σ_L, σ_b, v₀, n (and ω); the same c₀ in the threshold, the stepsize, (ii) and (iii); reason: universal constants depend on nothing; the literal and stronger reading
--   - reading: burn-in n₀ = n/2 → n₀ = n / 2 in ℕ (⌊n/2⌋); reason: n₀ is an integer parameter (p.12); for odd n the integer part is meant
--   - reading: the sample size condition of Theorem 1 → also n ≥ 2; reason: §3.1, p.12: "For a given sample size n ≥ 2"
--   - generalization: i.i.d. random pairs (L_i, b_i) of operators and vectors with E[L_i] = L, E[b_i] = b, through Φ_d L_i Φ_d^* and Φ_d b_i → i.i.d. square-integrable random pairs (A_i, h_i) ∈ ℝ^{d×d} × ℝ^d with E[A_i] = M, E[h_i] = Φ_d b (IsObsModel); reason: the algorithm (25), Assumption 1(W) and Σ* use the observations only through A_i = Φ_d L_i Φ_d^*, h_i = Φ_d b_i, and any paper instance yields such pairs (square-integrable by (11))
--   - generalization: a separable Hilbert space 𝕏 with an orthogonal basis {φ_j}_{j≥1} of 𝕏 such that 𝕊 = span{φ_1, …, φ_d} → any complete real inner product space 𝕏 (not necessarily separable) and an orthonormal basis φ_1, …, φ_d of 𝕊 only; reason: the statements involve only φ_1, …, φ_d; every paper instance is an instance of the Lean statement
--   - reading: (24a) "for t = 1, 2, …", n observations {(L_i, b_i)}_{i=1}^n → v₀ = Φ_d^*ϑ₀ deterministic in 𝕊, v_{t+1} uses observation t + 1, observations an infinite i.i.d. sequence indexed from 1; reason: Lemma 5 starts from v₀ and n observations must produce v_1, …, v_n; v_t = Φ_d^*ϑ_t (p.12) puts v₀ in 𝕊; Lemma 6's sum uses L_{n+1}
--   - encoding: E‖·‖² of a random vector → lower Lebesgue integral ∫⁻ ofReal ‖·‖² in [0, ∞]; reason: the expectation of a nonnegative random variable; the Lean form also asserts finiteness of the left side
--   - encoding: log²(x), e → Real.log x ^ 2, Real.exp 1; reason: Lean notation; the printed threshold's argument is used as printed; when v₀ = v̄ the printed log² is undefined (argument 0) and Lean's Real.log 0 = 0 makes (i) automatic, which only drops a condition, and the corrected bound holds there since (ii), (iii) suffice
--   - encoding: d unrestricted → 1 ≤ d; reason: λ_max and κ(M) are undefined for a 0 × 0 matrix (and η = 1/(c₀σ_L√(dn)) at d = 0); a nondegeneracy condition
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Eq. (45b), p.27, under the conditions of Theorem 1, p.13

import Mathlib
import Definitions.Def_ProjFPOracle_Phi
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_kappa
import Definitions.Def_ProjFPOracle_vbar
import Definitions.Def_ProjFPOracle_IsObsModel
import Definitions.Def_ProjFPOracle_Assumption1W
import Definitions.Def_ProjFPOracle_vhat
import Definitions.Def_ProjFPOracle_SigmaStar
import Definitions.Def_ProjFPOracle_En
import Definitions.Def_ProjFPOracle_Hn

open MeasureTheory

namespace ProjFPOracle

universe u v

/-- **The estimation-error bound, Eq. (45b), corrected** (Mou, Pananjady & Wainwright, *Optimal
Oracle Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (45b), p.27,
under the conditions of Theorem 1, p.13): "the estimation error is bounded as
`E‖v̂_n − v̄‖² ≤ c trace((I − M)⁻¹Σ^*(I − M)⁻ᵀ)/n + c (σ_L/(1 − κ)³)(d/n)^{3/2}(‖v̄‖²σ_L² + σ_b²)`",
for the algorithm (24) with stepsize `η = 1/(c_0 σ_L √(dn))`, burn-in `n_0 = n/2`, and
`n ≥ (c_0σ_L²d/(1−κ)²) log²(‖v_0 − v̄‖²d/(1−κ))`.

Two hypotheses are added, with the same universal `c_0`; without them the printed bound is false:
* (ii) `η < (1 − κ)/(4σ_L²d + 2(1 + |||L|||²_𝕏))` (the prescribed stepsize lies in Lemma 5's
  stability range; with `𝕏 = 𝕊 = ℝ`, `L = L_i ≡ m → −∞`, `b = b_i ≡ 0`, `v_0 = 1`, `n = 2`, the left
  side diverges while the threshold and the right side tend to `0`);
* (iii) `n ≥ (c_0σ_L²d/(1−κ)²) log²(e + ‖v_0 − v̄‖²(1 − κ)σ_L√n/(√d(‖v̄‖²σ_L² + σ_b²)))` (the sample
  size controls the initialization bias; with `𝕏 = 𝕊 = ℝ`, `L = L_i ≡ 0`, `b = b_i ≡ 0`, `v_0 = 1`,
  `σ_L = 1`, `σ_b = ε → 0`, the left side stays positive while the right side tends to `0`).

**Formalization Note** The constants `c_0, c > 0` are universal: they are chosen before the
dimension, the space, the operator, the law of the observations and the sample size, and the same
`c_0` appears in the threshold, the stepsize and (ii), (iii). The observations enter in projected
coordinates (`IsObsModel`, Assumption 1(W)); `n_0 = n/2` is natural-number division; `v_0 = Φ_d^* ϑ_0`
is deterministic; `log²` is the square of `Real.log`, and `e = exp 1`. The expectation of
`‖v̂_n − v̄‖²` is a lower Lebesgue integral in `[0, ∞]`. -/
theorem eq_45b :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) (b : X)
      {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω)
      (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ) (σL σb : ℝ)
      (ϑ₀ : Fin d → ℝ) (n : ℕ),
      1 ≤ d → IsUnit (1 - L) → kappa (projMat L φ) < 1 →
      IsObsModel P A h (projMat L φ) (Phi φ b) →
      Assumption1W P A h (projMat L φ) (Phi φ b) σL σb →
      2 ≤ n →
      let κ := kappa (projMat L φ)
      let η := 1 / (c₀ * σL * Real.sqrt ((d : ℝ) * n))
      let vb := vbar L b φ
      let v₀ := PhiStar φ ϑ₀
      -- (i) the printed sample-size threshold
      (n : ℝ) ≥ c₀ * σL ^ 2 * d / (1 - κ) ^ 2 * Real.log (‖v₀ - vb‖ ^ 2 * d / (1 - κ)) ^ 2 →
      -- (ii) added: the stepsize lies in Lemma 5's (corrected) range
      η < (1 - κ) / (4 * σL ^ 2 * d + 2 * (1 + ‖L‖ ^ 2)) →
      -- (iii) added: the sample size controls the initialization bias
      (n : ℝ) ≥ c₀ * σL ^ 2 * d / (1 - κ) ^ 2 *
        Real.log (Real.exp 1 + ‖v₀ - vb‖ ^ 2 * (1 - κ) * σL * Real.sqrt n /
          (Real.sqrt d * (‖vb‖ ^ 2 * σL ^ 2 + σb ^ 2))) ^ 2 →
      ∫⁻ ω, ENNReal.ofReal (‖vhat φ A h η ϑ₀ (n / 2) n ω - vb‖ ^ 2) ∂P ≤
        ENNReal.ofReal (c * En (projMat L φ) (SigmaStar φ L b P A h) n +
          c * Hn κ σL σb vb d n) := by sorry

end ProjFPOracle
