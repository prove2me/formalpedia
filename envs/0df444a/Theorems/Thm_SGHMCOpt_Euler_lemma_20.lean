-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_lemma_20
-- name    : SGHMCOpt.Euler.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:12.377108+00:00
-- url     : https://prove2.me/theorems/412aa460-6a30-48e4-a5dc-f27480dec687
-- title:
--   Lemma 20, p. 40 — bounding the initialization error: ℋ_ρ(μ₀, π_z) ≤ H̄_ρ(μ₀)
-- statement:
--   Assume parts (i)–(iv) of Assumption 1, the parameter conditions, the drift condition (2.2) with constant $A>0$, and let $(\alpha_1,\Lambda)$ solve (A.15). Let $\mu_0$ be a probability measure on $\mathbb R^d\times\mathbb R^d$ with finite second moment $\|(x,v)\|^2_{L^2(\mu_0)}=\int(\|x\|^2+\|v\|^2)\,d\mu_0$. Then for every dataset $z$ and every function $h$ of the class on p. 39 (with $R_1$ of (A.17)),
--   $$\mathcal H_\rho(\mu_0,\pi_z)\le\overline{\mathcal H}_\rho(\mu_0)=R_1+R_1\varepsilon_1\max\{\beta M+\tfrac12\beta\gamma^2,\tfrac34\beta\}\|(x,v)\|^2_{L^2(\mu_0)}+R_1\varepsilon_1(\beta M+\tfrac12\beta\gamma^2)\frac{b+d/\beta}m+R_1\varepsilon_1\tfrac34d+2R_1\varepsilon_1\Big(\beta A_0+\frac{\beta B^2}{2M}\Big),$$
--   where $\mathcal H_\rho$ is the semi-metric (A.12) built from $h$, $\alpha_1$, $\varepsilon_1$ of (A.16) and the Lyapunov function of $z$, and $\pi_z$ is the Gibbs law (1.7).
--
--   This replaces the quantity $\mathcal H_\rho(\mu_0,\pi_z)$ of Theorem 2, which depends on the dataset and on the function $h$ that Theorem 19 only asserts to exist, by an explicit bound uniform in $z$; it is what turns Theorem 2 into Corollary 4.
--
--   **Formalization Note** The paper's (A.18) prints the coefficient $M+\frac12\beta\gamma^2$ twice. The proof (p. 58) derives $\mathcal V(x,v)\le(\beta M+\frac12\beta\gamma^2)\|x\|^2+\frac34\beta\|v\|^2+\beta A_0+\beta B^2/(2M)$ and then drops the factor $\beta$ on $M$; the bound here uses $\beta M+\frac12\beta\gamma^2$, which is what the proof supports and is weaker than the printed one when $\beta>1$. The bound is claimed for every admissible $h$, because the proof uses only $h(r)\le\min\{r,R_1\}$. The finite second moment of $\mu_0$ is a hypothesis: the printed right side is infinite otherwise (it follows from Assumption 1 (v)).
-- source:
--   arXiv:1809.04618v4, Lemma 20, (A.18), p. 40; proof, p. 58

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model
import Definitions.Def_SGHMCOpt_Euler_Transport

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Lemma 20, p. 40, with the coefficient `βM + βγ²/2` of the proof (p. 58) in `H̄_ρ(μ₀)`:
under Assumption 1 (i)–(iv), for every dataset `z` and every function `h` of the class on p. 39
(with `R₁` of (A.17)), `ℋ_ρ(μ₀, π_z) ≤ H̄_ρ(μ₀)`, where `‖(x, v)‖²_{L²(μ₀)} = ∫(‖x‖² + ‖v‖²) dμ₀`. -/
theorem lemma_20 {d n : ℕ} {𝒵 𝒰 : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒰]
    (f : E d → 𝒵 → ℝ) (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (νU : Measure 𝒰)
    (μ0 : Measure (E d × E d)) (p : Params) (hn : 0 < n)
    (hloss : LossAssumption f p) (horacle : OracleAssumption f g νU p) (hpar : ParamCond p)
    (hdrift : DriftCond n f p) (hfix : FixedPt p d) (hμ0 : IsProbabilityMeasure μ0)
    (hm2 : Integrable (fun q : E d × E d => ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) μ0)
    (z : Fin n → 𝒵) (h : ℝ → ℝ) (hh : IsEGZProfile h (R1 p d)) :
    Hrho p h f z μ0 (gibbs p f z) ≤
      ENNReal.ofReal (Hbar p d (∫ q, (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) ∂μ0)) := by sorry

end SGHMCOpt.Euler
