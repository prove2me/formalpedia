-- Prove2me | Theorems.Thm_RandomReservoir_Static_theorem_1
-- name    : RandomReservoir.Static.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:46.311412+00:00
-- url     : https://prove2.me/theorems/73bf1c75-5ed4-4da2-a9fc-2c0cf3b72d54
-- title:
--   Theorem 1, pp. 37–38 — random ReLU networks with i.i.d. inner weights approximate Fourier-represented H* in L²(μ_Z) at rate C*/N
-- statement:
--   Let $\mathcal X$ be a separable real Hilbert space with its Borel $\sigma$-algebra, $m,N\ge1$, $M>0$, and $\sigma(x)=\max(x,0)$. Let $H^*:\mathcal X\to\mathbb R^m$ be represented on the ball of radius $M$ as
--   $$H_j^*(z)=\int_{\mathcal X}e^{i\langle w,z\rangle}\,\hat\mu_j(dw),\qquad \|z\|\le M,\ j=1,\dots,m,$$
--   for complex measures $\hat\mu_j(dw)=h_j(w)\,|\hat\mu_j|(dw)$ with (15): $\int\max(1,\|w\|^2)\,|\hat\mu_j|(dw)<\infty$. Let $\pi=\pi_{\mathcal X}\otimes(\pi_{\mathbb R}(x)\,dx)$ be a probability measure on $\mathcal X\times\mathbb R$ with $|\hat\mu_j|+|\hat\mu_j|^-\ll\pi_{\mathcal X}$, and with $F_\pi(x)=2\int_{-x}^0\pi_{\mathbb R}(u)^{-1}du$ let either
--
--   - (i) $\pi_{\mathbb R}>0$ and $|F_\pi(x)|<\infty$ for all $x\in\mathbb R$, or
--   - (ii) for some $R>0$, $\pi_{\mathcal X}(\{\|w\|>R\})=0$, and $\pi_{\mathbb R}(x)>0$, $|F_\pi(x)|<\infty$ for $|x|\le\max(MR,1)$.
--
--   Let $g_j=\frac{d(|\hat\mu_j|+|\hat\mu_j|^-)}{d\pi_{\mathcal X}}$ satisfy (16):
--   $$\int F_\pi(M\|w\|)\|w\|^2g_j(w)^2\,\pi_{\mathcal X}(dw)<\infty,\qquad\int\max(\|w\|^2,1)g_j(w)^2\,\pi_{\mathcal X}(dw)<\infty.$$
--   Let $(A_1,\zeta_1),\dots,(A_N,\zeta_N)$ be i.i.d. with law $\pi$, and let $Z$ be an $\mathcal X$-valued random variable with law $\mu_Z$, independent of them, with $\|Z\|\le M$ a.s. Put
--   $$C^*=\sum_{j=1}^mC^*_j,\quad C^*_j=M^2\!\int F_\pi(M\|w\|)\|w\|^2g_j^2\,d\pi_{\mathcal X}+32\max(M^2,1)\big(F_\pi(1)-F_\pi(-1)\big)\!\int\max(\|w\|^2,1)g_j^2\,d\pi_{\mathcal X}.$$
--   Then there is a readout $W$, an $\mathbb M_{m,N}$-valued random variable that is a measurable function of $(A,\zeta)$, such that the random ReLU network $H_W^{A,\zeta}(z)=W\sigma(Az+\zeta)$ satisfies
--   $$\mathbb E\big[\|H_W^{A,\zeta}(Z)-H^*(Z)\|^2\big]\le\frac{C^*}{N},$$
--   and for every $\delta\in(0,1)$, with probability at least $1-\delta$ over $(A,\zeta)$,
--   $$\Big(\int_{\mathcal X}\|H_W^{A,\zeta}(z)-H^*(z)\|^2\,\mu_Z(dz)\Big)^{1/2}\le\frac{\sqrt{C^*}}{\delta\sqrt N}.$$
--
--   This is the paper's random-feature approximation result in infinite dimensions. Only the linear readout is trained; the inner weights are sampled, and the error decays like $N^{-1/2}$ in $L^2$ with an explicit constant. Theorem 1 is the base for the finite-dimensional results of Section 4.2 and for the echo state network bounds.
--
--   **Formalization Note.**
--
--   1. *Constant.* The coefficient $32\max(M^2,1)$ replaces the printed $32M^2$. The printed constant is false for small $M$: take $\mathcal X=\mathbb R$, $m=N=1$, $H^*\equiv c\ne0$, $\pi_{\mathcal X}=\tfrac12\delta_0+\tfrac12\mathcal N(0,1)$, $\pi_{\mathbb R}$ the standard normal density, $Z\equiv0$. On $\{\zeta_1\le0\}$ every network vanishes, so the error is at least $c^2/2$, which exceeds the printed $C^*$ once $M<0.0127$. The two constants agree for $M\ge1$.
--   2. *Dropped claim.* The page's "$C^*>0$" is dropped: the explicit $C^*$ is $0$ for $H^*=0$, and stating the explicit value is the stronger claim.
--   3. *Randomness.* The inner weights $\theta=(\theta_1,\dots,\theta_N)$, $\theta_i=(A_i,\zeta_i)$, live on $(\mathcal X\times\mathbb R)^N$ with the product law $\pi^{\otimes N}$; $Z$ has its own law $\mu_Z$. By the standing independence of $Z$ and $(A,\zeta)$ (§4.1, p. 37) and Tonelli, the expectation is the iterated lower integral over $\pi^{\otimes N}$ and $\mu_Z$. "With probability $1-\delta$" is the statement that the bad set of $\theta$ has $\pi^{\otimes N}$-measure at most $\delta$.
--   4. *Readout.* $W$ is a measurable function of $\theta$ only, given by its entries; this is the paper's construction (22)–(23) and Remark 3. A readout allowed to depend on $Z$ would make the statement trivial.
--   5. *Polar form.* Complex measures are in polar form $\hat\mu_j=h_j\,\nu_j$ with $\nu_j=|\hat\mu_j|$ finite and $|h_j|=1$, which loses no generality (Rudin, Thm 6.12).
--   6. *Normalisation.* $\pi_{\mathcal X}$ is a probability measure and $\int\pi_{\mathbb R}=1$. Rescaling $\pi_{\mathcal X}$ by $c$ and $\pi_{\mathbb R}$ by $1/c$ leaves $\pi$ and $C^*$ unchanged, so this loses no generality.
--   7. *Encodings.* "$|F_\pi(x)|<\infty$" is integrability of $1/\pi_{\mathbb R}$ on the interval, and (15), (16) are stated as finite lower integrals and integrability, so none of them can hold vacuously.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Theorem 1, pp. 37–38; standing assumptions of §4.1, pp. 36–37; proof pp. 39–41

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory

/-- Theorem 1, Gonon–Grigoryeva–Ortega, Ann. Appl. Probab. 33 (2023), pp. 37–38, with the constant
`32·max(M², 1)` in place of the printed `32 M²`. The complex measures `μ̂_j` are given in polar form
`μ̂_j(dw) = h_j(w) ν_j(dw)` with `ν_j = |μ̂_j|` and `|h_j| = 1`. The inner weights `θ = (θ_1, …, θ_N)`,
`θ_i = (A_i, ζ_i)`, are i.i.d. with law `π`; the input `Z ~ μ_Z` is independent of them, so the
expectation is the iterated integral over `π^{⊗N}` and `μ_Z`. The readout `W = Wf θ` is a measurable
function of the inner weights only; `Wf θ` lists the entries `W_{j i}` (a matrix
in `M_{m,N}`, entrywise measurable). -/
theorem theorem_1
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (m N : ℕ) (hN : 0 < N) (M : ℝ) (hM : 0 < M)
    (Hstar : 𝒳 → Fin m → ℝ)
    (ν : Fin m → Measure 𝒳) (hν : ∀ j, IsFiniteMeasure (ν j))
    (h : Fin m → 𝒳 → ℂ) (hh_meas : ∀ j, Measurable (h j)) (hh_norm : ∀ j w, ‖h j w‖ = 1)
    (hrep : ∀ j (z : 𝒳), ‖z‖ ≤ M →
      (Hstar z j : ℂ) = ∫ w, Complex.exp (Complex.I * (inner ℝ w z : ℝ)) * h j w ∂(ν j))
    (h15 : ∀ j, ∫⁻ w, ENNReal.ofReal (max 1 (‖w‖ ^ 2)) ∂(ν j) < ⊤)
    (πX : Measure 𝒳) [IsProbabilityMeasure πX]
    (πR : ℝ → ℝ) (hπR_meas : Measurable πR) (hπR_nn : ∀ x, 0 ≤ πR x)
    (hπR_one : ∫ x, πR x = 1)
    (hac : ∀ j, ν j + (ν j).map (fun w => -w) ≪ πX)
    (hcase : SamplingCondition M πX πR)
    (h16a : ∀ j, Integrable (fun w => Fπ πR (M * ‖w‖) * ‖w‖ ^ 2 * gdens (ν j) πX w ^ 2) πX)
    (h16b : ∀ j, Integrable (fun w => max (‖w‖ ^ 2) 1 * gdens (ν j) πX w ^ 2) πX)
    (μZ : Measure 𝒳) [IsProbabilityMeasure μZ] (hZ : μZ {z | M < ‖z‖} = 0) :
    ∃ Wf : (Fin N → 𝒳 × ℝ) → Fin m → Fin N → ℝ, Measurable Wf ∧
      (∫⁻ θ, ∫⁻ z, ENNReal.ofReal (sqErr (network (Matrix.of (Wf θ)) θ z) (Hstar z)) ∂μZ
          ∂(Measure.pi fun _ : Fin N => samplingLaw πX πR))
        ≤ ENNReal.ofReal ((∑ j, CstarJ M πX πR (gdens (ν j) πX)) / N) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        (Measure.pi fun _ : Fin N => samplingLaw πX πR)
          {θ | ENNReal.ofReal (Real.sqrt (∑ j, CstarJ M πX πR (gdens (ν j) πX)) /
                (δ * Real.sqrt N)) <
              (∫⁻ z, ENNReal.ofReal (sqErr (network (Matrix.of (Wf θ)) θ z) (Hstar z)) ∂μZ) ^ (1 / 2 : ℝ)}
          ≤ ENNReal.ofReal δ := by sorry

end RandomReservoir.Static
