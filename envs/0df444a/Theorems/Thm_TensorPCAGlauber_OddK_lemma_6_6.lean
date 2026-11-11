-- Prove2me | Theorems.Thm_TensorPCAGlauber_OddK_lemma_6_6
-- name    : TensorPCAGlauber.OddK.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:55:31.516947+00:00
-- url     : https://prove2.me/theorems/3a315832-de30-45c3-95fc-8cc62e1c6840
-- title:
--   Lemma 6.6 — the average-gradient gauge transformation: $H_\varphi=H_{null}+H_{sig}$, $W$ independent of $(\varphi,R)$ with the law of $H_0^\perp$, and $Y_t(e)$ is Glauber dynamics for $H_\varphi$
-- statement:
--   Let $k\ge3$ be odd, $\beta>0$, $x^\star\in\Omega_N$, and let $\varphi,R,W$ be the gauge variables (eq. (71)), $m_\varphi(y)=m(x^\star\odot\varphi\odot y)$, $H_\varphi(y)=H(x^\star\odot\varphi\odot y)$. Then, for every realization of the Gaussian tensor,
--   $$m_\varphi(y)=\tfrac1N\langle\varphi,y\rangle,\qquad H_\varphi=H_{null}+H_{sig},\quad H_{null}(y)=\langle R,y\rangle+W(y),\quad H_{sig}(y)=N\lambda m_\varphi(y)^k-N\lambda\sigma_N^2m_\varphi(y).$$
--   Moreover: (1) $W$ is independent of $(\varphi,R)$ and has the same law as $H_0^\perp$; (2) for every $e\in\Omega_N$ and every realization of the disorder, the gauge-transformed trajectory $Y_t(e)=x^\star\odot\varphi\odot X_t(x^\star\odot\varphi\odot e)$ has the same law as Glauber dynamics for $H_\varphi$ at $\beta$ started at $Y_0=e$.
--
--   Differences from the source:
--   - encoding: $\Omega_N=\{\pm1\}^N$ → `Cube N = Fin N → Bool` with `true` ↦ +1, `false` ↦ −1 (`vec x` is the ±1 vector); reason: Lean convention; a bijection, same instances
--   - encoding: Glauber dynamics (Algorithm 3) as a process → the path `glauberPath` is a deterministic function of i.i.d. driving noise (Exp($N$) interarrivals, uniform site, uniform $[0,1]$ mark resolved against the heat-bath probability $q(+1\mid i,x)$); reason: the same law as Algorithm 3: $P[Z_n=+1]=q(+1\mid I_n,X_{T_n-})$; this is the construction §3.3 itself describes
--   - generalization: $\lambda=C_{\beta,k}N^\gamma$ (§6.2 standing assumption) → every real $\lambda$; reason: the proof uses no property of $\lambda$; the source's $\lambda$ is a special case
--   - encoding: "$W$ has the same law as $H_0^\perp$" → $P[W\in S]=P[H_0^\perp\in S]$ for every measurable $S\subseteq\mathbb R^{\Omega_N}$; reason: equality of laws without `Measure.map`
--   - encoding: "$Y_t(e)$ has the same law as Glauber dynamics for $H_\varphi$" → for each fixed Gaussian tensor: equal finite-dimensional distributions $P[Y_{t_j}(e)=s_j\ \forall j]$ of the two paths under the driving noise; reason: the law of a process on a finite state space is determined by its finite-dimensional distributions
--   - encoding: $N$ a dimension → hypothesis $1\le N$ (or $N\ge N_0$); reason: excludes only zero dimension, where $N^{-1}$ and $t/N$ are undefined
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 44 (PDF 47), Lemma 6.6 (definitions p. 44, eq. (71))

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber
import Definitions.Def_TensorPCAGlauber_OddK_Gauge

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- **Lemma 6.6** (Gauge-transformed Hamiltonian). With `m_φ(y) = m(x⋆ ⊙ φ ⊙ y)` and
`H_φ(y) = H(x⋆ ⊙ φ ⊙ y)`: `m_φ(y) = N^{−1}⟨φ, y⟩` and `H_φ = H_null + H_sig`, where
`H_null(y) = ⟨R, y⟩ + W(y)`, `W(y) = H_0^⊥(x⋆ ⊙ φ ⊙ y)`, `H_sig(y) = Nλ m_φ(y)^k − Nλσ²_N m_φ(y)`.
Moreover (1) `W` is independent of `(φ, R)` and has the law of `H_0^⊥`; (2) for every `e`, the
trajectory `Y_t(e)` has the law of Glauber dynamics for `H_φ` at `β` from `Y_0 = e`. -/
theorem lemma_6_6 (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N)
    (lam : ℝ) (xstar : Cube N) :
    (∀ (G' : KTensor k N) (y : Cube N),
        gaugeCorr xstar (gaugePhi k N lam xstar G') y
            = (N : ℝ)⁻¹ * dot (vec (gaugePhi k N lam xstar G')) (vec y) ∧
        gaugeH k N lam xstar G' y
            = Hnull (gaugeR k N lam xstar G') (gaugeW k N lam xstar G') y
              + Hsig k N lam (gaugePhi k N lam xstar G') y) ∧
    IndepFun (gaugeW k N lam xstar) (fun G' => (gaugePhi k N lam xstar G', gaugeR k N lam xstar G'))
      (disorderMeasure k N) ∧
    (∀ S : Set (Cube N → ℝ), MeasurableSet S →
        disorderMeasure k N (gaugeW k N lam xstar ⁻¹' S)
          = disorderMeasure k N (H0perp k N ⁻¹' S)) ∧
    (∀ (G' : KTensor k N) (e : Cube N) (n : ℕ) (ts : Fin n → ℝ) (s : Fin n → Cube N),
        noiseMeasure N {ω | ∀ j, gaugeTraj k N lam β xstar G' e ω (ts j) = s j}
          = noiseMeasure N {ω | ∀ j, glauberPath (gaugeH k N lam xstar G') β e ω (ts j) = s j}) := by sorry

end TensorPCAGlauber.OddK
