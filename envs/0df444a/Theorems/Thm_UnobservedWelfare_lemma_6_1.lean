-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_6_1
-- name    : UnobservedWelfare.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:07.819192+00:00
-- url     : https://prove2.me/theorems/05b0bed4-a1c2-474f-b9ac-3274be5369ce
-- title:
--   Lemma 6.1 — terminal history ratio (57)
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   On every path, both integrals below (over $\mathbb R^m_{++}$) are positive and finite, and
--   $$W\log\frac{\int e^{[c^*(z)-F_{w^+_T}(z)]/W}dz}{\int e^{-c^*(z)/W}dz}\ge-(m+2)W\log2.\tag{57}$$
--
--   It lower-bounds the history component of the terminal potential.
--
--   Differences from the source:
--   - generalization: (57) → (57) together with positivity (and finiteness) of both integrals; reason: positivity is the paper Lemma 4.4 and keeps the logarithm off the value $0$; dropping it gives (57)
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 6.1 (57), p.32 (PDF p.34)

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

/-- **Lemma 6.1 (terminal history ratio)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 6.1 (57), p.32 (PDF p.34)). Under
the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`, on every path the terminal history satisfies
`W log (∫ e^{[c*(z) − F_{w⁺_T}(z)]/W} dz / ∫ e^{−c*(z)/W} dz) ≥ −(m + 2)W log 2`, integrals over
`ℝ^m_{++}`.

**Formalization Note** The two integrals are `gibbsZ W (F_{w⁺_T} − c*)` and `gibbsZ W c*`. The
conclusion records that both are positive (hence the integrands integrable), so that the
logarithm is not evaluated at a junk `0`. -/
theorem lemma_6_1 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    ∀ ω,
      0 < gibbsZ W (fun z => E.surrPlus W c pstar T ω z - costConj c z) ∧
      0 < gibbsZ W (costConj c) ∧
      W * Real.log (gibbsZ W (fun z => E.surrPlus W c pstar T ω z - costConj c z) /
          gibbsZ W (costConj c)) ≥ -((m + 2) * W * Real.log 2) := by sorry

end UnobservedWelfare
