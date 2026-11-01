-- Prove2me | Theorems.Thm_ProjFPOracle_lemma_6
-- name    : ProjFPOracle.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:59.687776+00:00
-- url     : https://prove2.me/theorems/57711424-ca94-44fb-8c1a-f9e4a01b41e1
-- title:
--   Lemma 6, p.30 — decomposition of the error of the Polyak–Ruppert average $\widehat v_n$
-- statement:
--   Under the setting of Lemma 5 with a stepsize $0<\eta<(1-\kappa)/(4\sigma_L^2d+1+|||L|||_{\mathbb X}^2)$, a sample size $n\ge2$ and a burn-in time $n_0<n$, the Polyak–Ruppert average $\widehat v_n=\frac1{n-n_0}\sum_{t=n_0+1}^nv_t$ satisfies
--   $$
--   \begin{aligned}
--   \mathbb E\|\widehat v_n-\bar v\|^2\le{}&\frac6{n-n_0}\operatorname{trace}\big((I-M)^{-1}\Sigma^*(I-M)^{-\top}\big)\\
--   &+\frac6{(n-n_0)^2}\sum_{t=n_0}^n\mathbb E\big\|(I-M)^{-1}\Phi_d(L_{t+1}-L)(v_t-\bar v)\big\|_2^2+\frac{3\,\mathbb E\|v_n-v_{n_0}\|^2}{\eta^2(n-n_0)^2(1-\kappa)^2}.
--   \end{aligned}
--   $$
--   The first term is the covariance term that becomes $\mathcal E_n(M,\Sigma^*)$; the other two are controlled by Lemma 5 and give the higher-order term $\mathcal H_n$.
--
--   Differences from the source:
--   - reading: "Under the setup above" → Lemma 5's hypotheses with Lemma 5's printed range η ∈ (0, (1−κ)/(4σ_L²d + 1 + |||L|||²_𝕏)), n ≥ 2 (p.12) and any integer burn-in n₀ < n; reason: the setup of Lemma 5 just above; Lemma 6 holds on that range (|||(1 − η)I + ηM||| ≤ 1 there) and is false with no stepsize condition
--   - reading: Lemma/Theorem statement without the standing assumptions of §2.1 and §5.1 → hypotheses IsUnit (1 − L) and κ(M) < 1; reason: p.7 "We assume that the operator I − L has a bounded inverse"; p.28 "our assumption that κ(M) < 1"; the statements need both
--   - generalization: i.i.d. random pairs (L_i, b_i) of operators and vectors with E[L_i] = L, E[b_i] = b, through Φ_d L_i Φ_d^* and Φ_d b_i → i.i.d. square-integrable random pairs (A_i, h_i) ∈ ℝ^{d×d} × ℝ^d with E[A_i] = M, E[h_i] = Φ_d b (IsObsModel); reason: the algorithm (25), Assumption 1(W) and Σ* use the observations only through A_i = Φ_d L_i Φ_d^*, h_i = Φ_d b_i, and any paper instance yields such pairs (square-integrable by (11))
--   - generalization: a separable Hilbert space 𝕏 with an orthogonal basis {φ_j}_{j≥1} of 𝕏 such that 𝕊 = span{φ_1, …, φ_d} → any complete real inner product space 𝕏 (not necessarily separable) and an orthonormal basis φ_1, …, φ_d of 𝕊 only; reason: the statements involve only φ_1, …, φ_d; every paper instance is an instance of the Lean statement
--   - reading: (24a) "for t = 1, 2, …", n observations {(L_i, b_i)}_{i=1}^n → v₀ = Φ_d^*ϑ₀ deterministic in 𝕊, v_{t+1} uses observation t + 1, observations an infinite i.i.d. sequence indexed from 1; reason: Lemma 5 starts from v₀ and n observations must produce v_1, …, v_n; v_t = Φ_d^*ϑ_t (p.12) puts v₀ in 𝕊; Lemma 6's sum uses L_{n+1}
--   - encoding: ‖(I − M)⁻¹Φ_d(L_{t+1} − L)(v_t − v̄)‖²_2 → ∑_j (((1 − M)⁻¹ ((A_{t+1} − M)(ϑ_t − Φ_d v̄)))_j)²; reason: Φ_d(L_{t+1} − L)Φ_d^* = A_{t+1} − M and v_t − v̄ = Φ_d^*(ϑ_t − Φ_d v̄); the Euclidean norm squared written out
--   - encoding: E‖·‖² of a random vector → lower Lebesgue integral ∫⁻ ofReal ‖·‖² in [0, ∞]; reason: the expectation of a nonnegative random variable; the Lean form also asserts finiteness of the left side
--   - encoding: d unrestricted → 1 ≤ d; reason: λ_max and κ(M) are undefined for a 0 × 0 matrix (and η = 1/(c₀σ_L√(dn)) at d = 0); a nondegeneracy condition
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Lemma 6, p.30, Eq. (55)

import Mathlib
import Definitions.Def_ProjFPOracle_Phi
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_kappa
import Definitions.Def_ProjFPOracle_vbar
import Definitions.Def_ProjFPOracle_IsObsModel
import Definitions.Def_ProjFPOracle_Assumption1W
import Definitions.Def_ProjFPOracle_vhat
import Definitions.Def_ProjFPOracle_SigmaStar

open MeasureTheory Matrix

namespace ProjFPOracle

/-- **Lemma 6** (Mou, Pananjady & Wainwright, *Optimal Oracle Inequalities for Projected
Fixed-Point Equations*, arXiv:2012.05299v1, Lemma 6, p.30): "Under the setup above, we have the
bound
`E‖v̂_n − v̄‖² ≤ (6/(n − n_0)) trace((I − M)⁻¹Σ^*(I − M)⁻ᵀ)
  + (6/(n − n_0)²) ∑_{t=n_0}^n E‖(I − M)⁻¹Φ_d(L_{t+1} − L)(v_t − v̄)‖²_2
  + 3E‖v_n − v_{n_0}‖²/(η²(n − n_0)²(1 − κ)²)`." (55)

"The setup above" is that of Lemma 5 (p.30): `𝕏` a real Hilbert space, `𝕊` with orthonormal basis
`φ_1, …, φ_d` (`1 ≤ d`), `I − L` boundedly invertible, `M = Φ_d L Φ_d^*` with `κ = κ(M) < 1`,
i.i.d. unbiased observations (`IsObsModel`) satisfying Assumption 1(W), and a stepsize in Lemma 5's
printed range `η ∈ (0, (1−κ)/(4σ_L²d + 1 + |||L|||²_𝕏))`; the sample size is `n ≥ 2` (p.12) and the
burn-in `n_0 < n` is any integer.

**Formalization Note** In coordinates, `Φ_d(L_{t+1} − L)(v_t − v̄) = (A_{t+1} − M)(ϑ_t − Φ_d v̄)`,
and `‖·‖_2` on `ℝ^d` is written `∑_j (·)_j²`. Expectations of nonnegative quantities are lower
Lebesgue integrals in `[0, ∞]`. The sum runs from `t = n_0` to `t = n`, as printed (it uses
observation `n + 1`; the observation sequence is infinite). -/
theorem lemma_6 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) (b : X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ) (σL σb : ℝ)
    (ϑ₀ : Fin d → ℝ) (η : ℝ)
    (hd : 1 ≤ d) (hL : IsUnit (1 - L)) (hκ : kappa (projMat L φ) < 1)
    (hobs : IsObsModel P A h (projMat L φ) (Phi φ b))
    (hW : Assumption1W P A h (projMat L φ) (Phi φ b) σL σb)
    (hη₀ : 0 < η)
    (hη : η < (1 - kappa (projMat L φ)) / (4 * σL ^ 2 * d + 1 + ‖L‖ ^ 2))
    (n n₀ : ℕ) (hn : 2 ≤ n) (hn₀ : n₀ < n) :
    ∫⁻ ω, ENNReal.ofReal (‖vhat φ A h η ϑ₀ n₀ n ω - vbar L b φ‖ ^ 2) ∂P ≤
      ENNReal.ofReal (6 / ((n - n₀ : ℕ) : ℝ) *
          trace ((1 - projMat L φ)⁻¹ * SigmaStar φ L b P A h * ((1 - projMat L φ)⁻¹)ᵀ)) +
        ENNReal.ofReal (6 / ((n - n₀ : ℕ) : ℝ) ^ 2) *
          ∑ t ∈ Finset.Icc n₀ n, ∫⁻ ω, ENNReal.ofReal (∑ j, (((1 - projMat L φ)⁻¹ *ᵥ
            ((A (t + 1) ω - projMat L φ) *ᵥ (theta A h η ϑ₀ t ω - Phi φ (vbar L b φ)))) j) ^ 2) ∂P +
        ENNReal.ofReal (3 / (η ^ 2 * ((n - n₀ : ℕ) : ℝ) ^ 2 * (1 - kappa (projMat L φ)) ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (‖vIter φ A h η ϑ₀ n ω - vIter φ A h η ϑ₀ n₀ ω‖ ^ 2) ∂P := by sorry

end ProjFPOracle
