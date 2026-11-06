-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_6_2
-- name    : UnobservedWelfare.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:24.444412+00:00
-- url     : https://prove2.me/theorems/31b342bc-aa0d-4237-a440-91ba19d474a0
-- title:
--   Lemma 6.2 — terminal inventory ratio (58)
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   On every path, $q_1\gg0$, both integrals below (over $\mathbb R^m_{++}$) are positive and finite, and
--   $$\kappa W\log\frac{\int e^{-[I_T\cdot z+\Gamma_{w^+_T}(z)]/(\kappa W)}dz}{\int e^{-q_1\cdot z/(\kappa W)}dz}\ge-2\kappa mW\log T-\kappa mW\log\Big(3+\frac{6+\gamma}{\kappa}\Big)-\gamma W.\tag{58}$$
--
--   Together with Lemma 6.1 it gives estimate (III) of Lemma 3.2 with $C=2\kappa$.
--
--   Differences from the source:
--   - generalization: $q_1\gg0$ and (58) → $q_1\gg0$, (58), and positivity (and finiteness) of both integrals; reason: positivity is the paper Lemma 4.4 and keeps the logarithm off the value $0$; dropping it gives the source statement
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 6.2 (58), p.33 (PDF p.35)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_gibbsMean
import Definitions.Def_UnobservedWelfare_alg1
import Definitions.Def_UnobservedWelfare_roundLoss
import Definitions.Def_UnobservedWelfare_potential

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 6.2 (terminal inventory ratio)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 6.2 (58), p.33 (PDF p.35)). Under
the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`, on every path the initial production satisfies `q_1 ≫ 0`, and
`κW log (∫ e^{−[I_T·z + Γ_{w⁺_T}(z)]/(κW)} dz / ∫ e^{−q_1·z/(κW)} dz)
  ≥ −2κmW log T − κmW log(3 + (6 + γ)/κ) − γW`, integrals over `ℝ^m_{++}`.

**Formalization Note** `q_1` is the execution's round-`0` production. The conclusion records that
both integrals are positive (hence the integrands integrable), so that the logarithm is not
evaluated at a junk `0`. -/
theorem lemma_6_2 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    ∀ ω,
      E.q 0 ω ∈ posOrthant m ∧
      0 < gibbsZ (κ * W) (fun z => E.invAfter T ω ⬝ᵥ z + E.gamPlus W γ T ω z) ∧
      0 < gibbsZ (κ * W) (fun z => E.q 0 ω ⬝ᵥ z) ∧
      κ * W * Real.log (gibbsZ (κ * W) (fun z => E.invAfter T ω ⬝ᵥ z + E.gamPlus W γ T ω z) /
          gibbsZ (κ * W) (fun z => E.q 0 ω ⬝ᵥ z))
        ≥ -2 * κ * m * W * Real.log T - κ * m * W * Real.log (3 + (6 + γ) / κ) - γ * W := by sorry

end UnobservedWelfare
