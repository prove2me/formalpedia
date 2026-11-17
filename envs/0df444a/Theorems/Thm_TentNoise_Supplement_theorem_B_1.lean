-- Prove2me | Theorems.Thm_TentNoise_Supplement_theorem_B_1
-- name    : TentNoise.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:45:47.624892+00:00
-- url     : https://prove2.me/theorems/c47b8201-7fd3-4ae8-89c1-20c01e0f7868
-- title:
--   Theorem B.1 — no-noise lower bound: $W_{1,\rho_{1,T}}(\mathbb P_T,\mathbb Q^g_T)\ge c$ at a horizon $T=O(1/\varepsilon_P)$
-- statement:
--   Let $f(x)=1-2|x-\tfrac12|$ be the tent map on $[0,1]$, $\mu=\mathrm{Unif}[0,1]$ its invariant law, and for a horizon $T\ge1$ let $\mathbb P_T$ be the law of the true path $(X_0,\dots,X_T)$ with $X_0\sim\mu$, $X_{t+1}=f(X_t)$. For a fitted map $g:[0,1]\to[0,1]$, $\mathbb Q^g_T$ is the law of the deterministic rollout $X_0\sim\mu$, $X_{t+1}=g(X_t)$ (no noise), and $\|f-g\|_2$ is the $L^2(\mu)$ one-step error. Paths are compared with the Wasserstein distance $W_{1,\rho_{1,T}}$ for the normalized path metric $\rho_{1,T}(x,y)=\frac1{T+1}\sum_{t=0}^T|x_t-y_t|$.
--
--   **Theorem B.1 (Lower bound for no noise).** There are a universal constant $c>0$ and a constant $C$ such that for every $0<\varepsilon_P\le 1/2$ there are a Borel map $g_{\varepsilon_P}:[0,1]\to[0,1]$ and an integer horizon $1\le T_{\varepsilon_P}\le C/\varepsilon_P$ with $\|f-g_{\varepsilon_P}\|_2\le\varepsilon_P$ and
--
--   $$
--   W_{1,\rho_{1,T_{\varepsilon_P}}}\bigl(\mathbb P_{T_{\varepsilon_P}},\mathbb Q^{g_{\varepsilon_P}}_{T_{\varepsilon_P}}\bigr)\ge c .
--   $$
--
--   Without noise, an arbitrarily accurate next-step predictor can still produce rollouts whose path law stays a constant distance from the truth at a horizon of order $1/\varepsilon_P$. This is the deterministic separation that motivates inference-time noising; the paper states the same result as Theorem 3.2 (p.7).
--
--   **Formalization Note** $\mathbb Q^g_T$ is the base mission's noised path law at noise level $\sigma=0$. The constants $c$ and $C$ are fixed before $\varepsilon_P$; $g$ and $T$ are chosen after it.
--
--   Differences from the source:
--   - reading: an integer T_ε = O(1/ε_P), for some universal constant c → ∃ c > 0, ∃ C, ∀ ε ∈ (0, 1/2], ∃ g, ∃ T : ℕ with 1 ≤ T ≤ C / ε; c and C fixed before ε, g and T after; reason: the standard reading of O(·) with a constant uniform in ε over the stated range (the proof gives explicit constants); c > 0 because c ≤ 0 makes the bound vacuous; T ≥ 1 because the path distance is defined for horizons T ≥ 1 (the proof's horizon is at least 3)
--   - encoding: a map g_ε : [0,1] → [0,1] (Borel, the paper's fitted maps); ℚ^{g}_T the noiseless rollout → g : ℝ → ℝ with a measurability proof and MapsTo g [0,1] [0,1]; ℚ^g_T = noisedLaw g hg 0 T (H₀(x,·) = δ_x on [0,1]); reason: values of g off [0,1] are never visited; the base mission's convention; same instances
--   - encoding: W_{1,ρ1,T}(ℙ_T, ℚ^g_T) ≥ c (a real number) → ENNReal.ofReal c ≤ pathW1 T (trueLaw T) (noisedLaw g hg 0 T); reason: the published path Wasserstein distance is ℝ≥0∞-valued; same content for c > 0
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Theorem B.1, p.23 (PDF p.23), eq. (57); same statement as Theorem 3.2, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP

open MeasureTheory ProbabilityTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise.Supplement

/-- **Theorem B.1 (Lower bound for no noise)** (Huan, Risteski, Wei, *Mitigating error propagation
in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission
(manuscript sha256 67925b3e…), Theorem B.1, p.23, eq. (57); the same statement is Theorem 3.2, p.7):
for every `0 < ε_P ≤ 1/2` there are a map `g_{ε_P}` and an integer `T_{ε_P} = O(1/ε_P)` with
`‖f − g_{ε_P}‖₂ ≤ ε_P` and `W_{1,ρ_{1,T}}(ℙ_T, ℚ^{g}_T) ≥ c` at `T = T_{ε_P}`, for a universal constant `c`.

**Formalization Note** `ℚ^g_T` is the deterministic rollout `ℚ^{g,0}_T = noisedLaw g hg 0 T`
(no noise). The universal constant `c > 0` and the `O(·)` constant `C` are fixed before `ε`;
`g` and `T` are chosen after `ε`; `T = O(1/ε)` is `1 ≤ T ≤ C / ε` on the whole range `(0, 1/2]`.
`g : ℝ → ℝ` is Borel with `g([0,1]) ⊆ [0,1]` (the paper's `g : [0,1] → [0,1]`); `‖f − g‖₂` is
`errP g`, the `L²(µ)` norm (not its square). `W` is `ℝ≥0∞`-valued, so `c` enters as `ofReal c`. -/
theorem theorem_B_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (g : ℝ → ℝ) (hg : Measurable g) (T : ℕ),
        MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1) ∧
        errP g ≤ ε ∧
        1 ≤ T ∧ (T : ℝ) ≤ C / ε ∧
        ENNReal.ofReal c ≤ pathW1 T (trueLaw T) (noisedLaw g hg 0 T) := by sorry

end TentNoise.Supplement
