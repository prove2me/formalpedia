-- Prove2me | Theorems.Thm_TentNoise_theorem_3_1
-- name    : TentNoise.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:12.459652+00:00
-- url     : https://prove2.me/theorems/c5dc0ae1-d337-482d-a753-0eca32bdc7be
-- title:
--   Theorem 3.1 — noise $\sigma^*=4\sqrt{\varepsilon_P}$ gives $W_{1,\rho_{1,T}}(\mathbb P_T,\mathbb Q^{\sigma^*}_T)\le4\sqrt{\varepsilon_P}$ for every $T$, and $\sqrt{\varepsilon_P}$ is optimal
-- statement:
--   Let $f(x)=1-2|x-\tfrac12|$ be the tent map with invariant law $\mu=\mathrm{Unif}[0,1]$, let $\mathbb P_T$ be the law of its stationary path $(X_0,\dots,X_T)$, and for a Borel map $g:[0,1]\to[0,1]$ with one-step error $\varepsilon_P=\|f-g\|_{L^2(\mu)}$ let $\mathbb Q^{g,\sigma}_T$ be the law of the rollout $X_0\sim\mu$, $X_{t+1}=\mathfrak r(g(X_t)+\sigma Z_{t+1})$ with i.i.d. standard Gaussians $Z_t$ and the folding reflection $\mathfrak r$.
--
--   1. For every $T\ge1$ and $\sigma^*=4\sqrt{\varepsilon_P}$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb Q^{g,\sigma^*}_T\bigr)\le4\sqrt{\varepsilon_P}.
--   $$
--
--   2. This choice of $\sigma^*$ achieves the asymptotically optimal worst-case rate in $\varepsilon_P$ among constant reflected-Gaussian noise levels: there are universal constants $c>0$ and $\varepsilon_0>0$ such that, for every $0<\varepsilon_P\le\varepsilon_0$, there are a Lipschitz map $g_{\varepsilon_P}$ and an integer $T_{\varepsilon_P}=O(\log(1/\varepsilon_P))$ with $(g_{\varepsilon_P})_\#\mu=\mu$, $\mathrm{Lip}(g_{\varepsilon_P})<3$, $\|f-g_{\varepsilon_P}\|_2=\varepsilon_P$, and
--
--   $$
--   \inf_{\sigma\ge0}W_{1,\rho_{1,T_{\varepsilon_P}}}\bigl(\mathbb P_{T_{\varepsilon_P}},\mathbb Q^{g_{\varepsilon_P},\sigma}_{T_{\varepsilon_P}}\bigr)\ge c\sqrt{\varepsilon_P}.
--   $$
--
--   Here $W_{1,\rho_{1,T}}$ is the Wasserstein distance on path space for the length-normalized metric $\rho_{1,T}(x,y)=\frac1{T+1}\sum_t|x_t-y_t|$. Inference-time noise converts one-step accuracy into accuracy of the whole trajectory law, uniformly in the horizon, even though the tent map amplifies errors exponentially forward in time.
--
--   **Formalization Note** The first clause is for every Borel $g$ with $g([0,1])\subseteq[0,1]$ and no other hypothesis, including $\varepsilon_P=0$. In the second clause, $c$, $\varepsilon_0$ and the constant $C$ of $O(\log(1/\varepsilon_P))$ are fixed before $\varepsilon_P$, and $g$ and $T$ before $\sigma$.
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] Borel; paths in [0,1]^{T+1} → g : ℝ → ℝ measurable with g([0,1]) ⊆ [0,1]; paths Fin (T+1) → ℝ; reason: every path law is concentrated on [0,1]^{T+1} and values of g off [0,1] are never visited; every Borel map of [0,1] extends to a Borel map of ℝ
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
--   - reading: T_ε = O(log(1/ε)), an integer → 1 ≤ T_ε ≤ C log(1/ε), with C fixed (like c and ε₀) before ε; reason: the standard reading of O(·) as ε → 0 with a constant uniform in ε; T_ε ≥ 1 because the path distance and Theorem 3.1 are for horizons T ≥ 1 (the paper's T_ε = 2(k+1) ≥ 2)
--   - encoding: inf_{σ≥0} W ≥ c√ε → ∀ σ ≥ 0, ofReal(c√ε) ≤ W; reason: equivalent; g_ε and T_ε are chosen before σ
--   - encoding: map g_ε of [0,1] with (g_ε)#µ = µ and Lip(g_ε) < 3 → g_ε : ℝ → ℝ Borel with g_ε([0,1]) ⊆ [0,1], µ.map g_ε = µ, ∃ K < 3 LipschitzOnWith K g_ε [0,1]; reason: values off [0,1] are never visited; same instances
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Theorem 3.1, p.6 (PDF p.6), eqs. (11)–(12)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Theorem 3.1 (Main, `W_{1,ρ_{1,T}}` distance)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Theorem 3.1, p.6, eqs. (11)–(12)).
For every `T ≥ 1` and `σ* = 4√ε_P`, `W_{1,ρ_{1,T}}(ℙ_T, ℚ^{σ*}_T) ≤ 4√ε_P`. Moreover this choice of `σ*`
achieves the asymptotically optimal worst-case rate in `ε_P` among constant reflected-Gaussian noise
levels: there are universal constants `c > 0` and `ε₀ > 0` such that, for every `0 < ε_P ≤ ε₀`, there
are a Lipschitz map `g_{ε_P}` and an integer `T_{ε_P} = O(log(1/ε_P))` with `(g_{ε_P})_#µ = µ`,
`Lip(g_{ε_P}) < 3`, `‖f − g_{ε_P}‖₂ = ε_P`, and `inf_{σ≥0} W_{1,ρ_{1,T}}(ℙ_T, ℚ^{g,σ}_T) ≥ c√ε_P`
at `T = T_{ε_P}`.

**Formalization Note** First clause: every Borel `g : ℝ → ℝ` with `g([0,1]) ⊆ [0,1]` (the paper's
Borel `g : [0,1] → [0,1]`, §2.4), no other hypothesis, every `T ≥ 1`, including `ε_P = 0`. Second
clause: `T = O(log(1/ε))` is `T ≤ C log(1/ε)` with `C` fixed, like `c` and `ε₀`, before `ε`; `g` and `T`
are chosen before `σ`; the infimum over `σ ≥ 0` is a bound for every `σ ≥ 0`, including `σ = 0`.
`Lip < 3` is a Lipschitz constant `K < 3` on `[0, 1]` (which makes `g` Lipschitz). `T ≥ 1`. -/
theorem theorem_3_1 :
    (∀ (g : ℝ → ℝ) (hg : Measurable g), MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1) →
      ∀ T : ℕ, 1 ≤ T →
        pathW1 T (trueLaw T) (noisedLaw g hg (4 * Real.sqrt (errP g)) T) ≤
          ENNReal.ofReal (4 * Real.sqrt (errP g))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (g : ℝ → ℝ) (hg : Measurable g) (T : ℕ),
        MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1) ∧
        unifI.map g = unifI ∧
        (∃ K : ℝ≥0, (K : ℝ) < 3 ∧ LipschitzOnWith K g (Icc (0 : ℝ) 1)) ∧
        errP g = ε ∧
        1 ≤ T ∧ (T : ℝ) ≤ C * Real.log (1 / ε) ∧
        ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (c * Real.sqrt ε) ≤ pathW1 T (trueLaw T) (noisedLaw g hg σ T)) := by sorry

end TentNoise
