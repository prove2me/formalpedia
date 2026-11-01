-- Prove2me | Theorems.Thm_ProjFPOracle_lemma_5
-- name    : ProjFPOracle.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:16.142921+00:00
-- url     : https://prove2.me/theorems/79ca5fe1-bc5e-4d60-b00d-5ff6ddd3738c
-- title:
--   Lemma 5, p.30 (corrected: stepsize range $\eta<(1-\kappa)/(4\sigma_L^2d+2(1+|||L|||^2))$) — mean-square error of the iterates
-- statement:
--   Let $\mathbb X$ be a real Hilbert space, $\mathbb S$ a subspace with orthonormal basis $\varphi_1,\dots,\varphi_d$ ($d\ge1$), $L$ a bounded operator with $I-L$ boundedly invertible, $b\in\mathbb X$, $M=\Phi_dL\Phi_d^*$ with $\kappa=\kappa(M)<1$, and $\bar v$ the projected fixed point. Let the observations be i.i.d. and unbiased and satisfy Assumption 1(W) with $\sigma_L,\sigma_b>0$, and let $v_t$ be the stochastic approximation iterates started at a fixed $v_0\in\mathbb S$. Then for every stepsize
--   $$
--   0<\eta<\frac{1-\kappa}{4\sigma_L^2d+2\big(1+|||L|||_{\mathbb X}^2\big)}
--   $$
--   and every $t=1,2,\dots$,
--   $$
--   \mathbb E\|v_t-\bar v\|^2\le e^{-(1-\kappa)\eta t/2}\,\|v_0-\bar v\|^2+\frac{8\eta}{1-\kappa}\big(\|\bar v\|^2\sigma_L^2d+\sigma_b^2d\big).
--   $$
--   The iterates forget their initialization geometrically and settle at a noise floor proportional to $\eta$; Theorem 1 uses this bound for the iterates after the burn-in time.
--
--   The printed stepsize range has $1+|||L|||_{\mathbb X}^2$ in place of $2(1+|||L|||_{\mathbb X}^2)$, and is too wide when $\kappa<0$ (see the correction below).
--
--   Differences from the source:
--   - correction: η ∈ (0, (1−κ)/(4σ_L²d + 1 + |||L|||²_𝕏)) → η ∈ (0, (1−κ)/(4σ_L²d + 2(1 + |||L|||²_𝕏))); reason: the printed range is false for κ < 0: 𝕏 = 𝕊 = ℝ, L = L_i ≡ −1, b = b_i ≡ 0, σ_L = σ_b = 0.1, v₀ = 1, η = 0.95 (inside the printed range 0.980) gives E‖v₁ − v̄‖² = 0.81 > e^{−0.95} + 0.038 = 0.425
--   - reading: Lemma/Theorem statement without the standing assumptions of §2.1 and §5.1 → hypotheses IsUnit (1 − L) and κ(M) < 1; reason: p.7 "We assume that the operator I − L has a bounded inverse"; p.28 "our assumption that κ(M) < 1"; the statements need both
--   - generalization: i.i.d. random pairs (L_i, b_i) of operators and vectors with E[L_i] = L, E[b_i] = b, through Φ_d L_i Φ_d^* and Φ_d b_i → i.i.d. square-integrable random pairs (A_i, h_i) ∈ ℝ^{d×d} × ℝ^d with E[A_i] = M, E[h_i] = Φ_d b (IsObsModel); reason: the algorithm (25), Assumption 1(W) and Σ* use the observations only through A_i = Φ_d L_i Φ_d^*, h_i = Φ_d b_i, and any paper instance yields such pairs (square-integrable by (11))
--   - generalization: a separable Hilbert space 𝕏 with an orthogonal basis {φ_j}_{j≥1} of 𝕏 such that 𝕊 = span{φ_1, …, φ_d} → any complete real inner product space 𝕏 (not necessarily separable) and an orthonormal basis φ_1, …, φ_d of 𝕊 only; reason: the statements involve only φ_1, …, φ_d; every paper instance is an instance of the Lean statement
--   - reading: (24a) "for t = 1, 2, …", n observations {(L_i, b_i)}_{i=1}^n → v₀ = Φ_d^*ϑ₀ deterministic in 𝕊, v_{t+1} uses observation t + 1, observations an infinite i.i.d. sequence indexed from 1; reason: Lemma 5 starts from v₀ and n observations must produce v_1, …, v_n; v_t = Φ_d^*ϑ_t (p.12) puts v₀ in 𝕊; Lemma 6's sum uses L_{n+1}
--   - encoding: E‖v₀ − v̄‖² → ‖v₀ − v̄‖² with v₀ = Φ_d^*ϑ₀; reason: v₀ is deterministic (R2), so the expectation is the value
--   - encoding: E‖·‖² of a random vector → lower Lebesgue integral ∫⁻ ofReal ‖·‖² in [0, ∞]; reason: the expectation of a nonnegative random variable; the Lean form also asserts finiteness of the left side
--   - encoding: d unrestricted → 1 ≤ d; reason: λ_max and κ(M) are undefined for a 0 × 0 matrix (and η = 1/(c₀σ_L√(dn)) at d = 0); a nondegeneracy condition
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Lemma 5, p.30, Eq. (54)

import Mathlib
import Definitions.Def_ProjFPOracle_Phi
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_kappa
import Definitions.Def_ProjFPOracle_vbar
import Definitions.Def_ProjFPOracle_IsObsModel
import Definitions.Def_ProjFPOracle_Assumption1W
import Definitions.Def_ProjFPOracle_vhat

open MeasureTheory

namespace ProjFPOracle

/-- **Lemma 5, with the corrected stepsize range** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Lemma 5, p.30): "Suppose
that the noise conditions in Assumption 1(W) hold. Then for any stepsize
`η ∈ (0, (1−κ)/(4σ_L²d + 1 + |||L|||²_𝕏))`, we have the bound
`E‖v_t − v̄‖² ≤ e^{−(1−κ)ηt/2} E‖v_0 − v̄‖² + (8η/(1−κ))(‖v̄‖²σ_L²d + σ_b²d)` valid for
`t = 1, 2, …`." (54)

Here the range is `η ∈ (0, (1−κ)/(4σ_L²d + 2(1 + |||L|||²_𝕏)))`: the printed range is too wide when
`κ < 0` (with `𝕏 = 𝕊 = ℝ`, `L = L_i ≡ −1`, `b = b_i ≡ 0`, `σ_L = σ_b = 0.1`, `v_0 = 1`, `η = 0.95`:
`E‖v_1 − v̄‖² = 0.81` exceeds the printed bound `0.425`).

Setting: `𝕏` a real Hilbert space, `𝕊` with orthonormal basis `φ_1, …, φ_d` (`1 ≤ d`), `I − L`
boundedly invertible, `M = Φ_d L Φ_d^*` with `κ = κ(M) < 1`; i.i.d. unbiased observations in the
coordinates `A_i = Φ_d L_i Φ_d^*`, `h_i = Φ_d b_i` (`IsObsModel`) satisfying Assumption 1(W) with
`σ_L, σ_b > 0`; `v_t = Φ_d^* ϑ_t` the iterates (24a)/(25) from the deterministic `v_0 = Φ_d^* ϑ_0`.

**Formalization Note** Expectations of the nonnegative quantities `‖v_t − v̄‖²` are lower Lebesgue
integrals in `[0, ∞]`, so the statement also asserts they are finite. Since `v_0` is deterministic,
`E‖v_0 − v̄‖² = ‖v_0 − v̄‖²`. -/
theorem lemma_5 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) (b : X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ) (σL σb : ℝ)
    (ϑ₀ : Fin d → ℝ) (η : ℝ)
    (hd : 1 ≤ d) (hL : IsUnit (1 - L)) (hκ : kappa (projMat L φ) < 1)
    (hobs : IsObsModel P A h (projMat L φ) (Phi φ b))
    (hW : Assumption1W P A h (projMat L φ) (Phi φ b) σL σb)
    (hη₀ : 0 < η)
    (hη : η < (1 - kappa (projMat L φ)) / (4 * σL ^ 2 * d + 2 * (1 + ‖L‖ ^ 2)))
    (t : ℕ) (ht : 1 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (‖vIter φ A h η ϑ₀ t ω - vbar L b φ‖ ^ 2) ∂P ≤
      ENNReal.ofReal
        (Real.exp (-(1 - kappa (projMat L φ)) * η * t / 2) * ‖PhiStar φ ϑ₀ - vbar L b φ‖ ^ 2 +
          8 * η / (1 - kappa (projMat L φ)) *
            (‖vbar L b φ‖ ^ 2 * σL ^ 2 * d + σb ^ 2 * d)) := by sorry

end ProjFPOracle
