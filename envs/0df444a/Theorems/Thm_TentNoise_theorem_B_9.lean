-- Prove2me | Theorems.Thm_TentNoise_theorem_B_9
-- name    : TentNoise.theorem_B_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:24.102379+00:00
-- url     : https://prove2.me/theorems/3a8f3319-d692-4e8d-bab8-bad92599f70b
-- title:
--   Theorem B.9 — lower bound $\inf_{\sigma\ge0}W_{1,\rho_{1,T_\varepsilon}}\ge c\sqrt\varepsilon$ for every constant noise level
-- statement:
--   There are universal constants $c>0$ and $\varepsilon_0>0$ such that, for every $0<\varepsilon\le\varepsilon_0$, there are a continuous map $g_\varepsilon$ and an integer $T_\varepsilon=O(\log(1/\varepsilon))$ satisfying
--
--   $$
--   (g_\varepsilon)_\#\mu=\mu,\qquad \mathrm{Lip}(g_\varepsilon)<3,\qquad \|g_\varepsilon-f\|_2=\varepsilon,
--   $$
--
--   and
--
--   $$
--   \inf_{\sigma\ge0}W_{1,\rho_{1,T_\varepsilon}}\bigl(\mathbb P_{T_\varepsilon},\mathbb Q^{g_\varepsilon,\sigma}_{T_\varepsilon}\bigr)\ge c\sqrt\varepsilon .
--   $$
--
--   No constant level of reflected Gaussian noise can do better than $\sqrt\varepsilon$, so the rate of Theorem A.10 is optimal; the obstruction already appears at a logarithmic horizon.
--
--   **Formalization Note** $T_\varepsilon=O(\log(1/\varepsilon))$ means $T_\varepsilon\le C\log(1/\varepsilon)$ with $C$ fixed, like $c$ and $\varepsilon_0$, before $\varepsilon$. The infimum over $\sigma\ge0$ includes $\sigma=0$, the deterministic rollout.
--
--   Differences from the source:
--   - reading: T_ε = O(log(1/ε)), an integer → 1 ≤ T_ε ≤ C log(1/ε), with C fixed (like c and ε₀) before ε; reason: the standard reading of O(·) as ε → 0 with a constant uniform in ε; T_ε ≥ 1 because the path distance and Theorem 3.1 are for horizons T ≥ 1 (the paper's T_ε = 2(k+1) ≥ 2)
--   - encoding: inf_{σ≥0} W ≥ c√ε → ∀ σ ≥ 0, ofReal(c√ε) ≤ W; reason: equivalent; g_ε and T_ε are chosen before σ
--   - encoding: map g_ε of [0,1] with (g_ε)#µ = µ and Lip(g_ε) < 3 → g_ε : ℝ → ℝ Borel with g_ε([0,1]) ⊆ [0,1], µ.map g_ε = µ, ∃ K < 3 LipschitzOnWith K g_ε [0,1]; reason: values off [0,1] are never visited; same instances
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Theorem B.9, p.32 (PDF p.32), eq. (78)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Theorem B.9 (Lower bound for every constant reflected-Gaussian noise level)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…),
Theorem B.9, p.32, eq. (78)): there are universal constants `c > 0` and `ε₀ > 0` such that, for every
`0 < ε ≤ ε₀`, there are a continuous map `g_ε` and an integer `T_ε = O(log(1/ε))` with
`(g_ε)_#µ = µ`, `Lip(g_ε) < 3`, `‖g_ε − f‖₂ = ε`, and `inf_{σ≥0} W_{1,ρ_{1,T_ε}}(ℙ_{T_ε}, ℚ^{g_ε,σ}_{T_ε}) ≥ c√ε`.

**Formalization Note** `T_ε = O(log(1/ε))` is `T_ε ≤ C log(1/ε)` with `C` fixed, like `c` and `ε₀`,
before `ε`; `g_ε` and `T_ε` are chosen before `σ`, and the infimum over `σ ≥ 0` is a bound for every
`σ ≥ 0`, including `σ = 0`. `g_ε : ℝ → ℝ` is Borel with `g_ε([0,1]) ⊆ [0,1]`; `Lip(g_ε) < 3` is a
Lipschitz constant `K < 3` on `[0, 1]`. `T_ε ≥ 1` (the paper's `T_ε = 2(k+1)`). -/
theorem theorem_B_9 :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (g : ℝ → ℝ) (hg : Measurable g) (T : ℕ),
        ContinuousOn g (Icc 0 1) ∧
        MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1) ∧
        unifI.map g = unifI ∧
        (∃ K : ℝ≥0, (K : ℝ) < 3 ∧ LipschitzOnWith K g (Icc (0 : ℝ) 1)) ∧
        errP g = ε ∧
        1 ≤ T ∧ (T : ℝ) ≤ C * Real.log (1 / ε) ∧
        ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (c * Real.sqrt ε) ≤ pathW1 T (trueLaw T) (noisedLaw g hg σ T) := by sorry

end TentNoise
