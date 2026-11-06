-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_5_4
-- name    : UnobservedWelfare.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:24.776901+00:00
-- url     : https://prove2.me/theorems/da816781-6c21-4c2e-b705-f182a9ff6937
-- title:
--   Lemma 5.4 — population energy $R_M$, (53) and (54)
-- statement:
--   Throughout, $c$ is an admissible cost, the buyer model on a standard Borel type space satisfies RC at scale $W>0$ and is centered ($S_\theta(1)=0$), $p^\star$ is a comparison price (34), $0<\gamma\le1$, $\kappa\ge80/\gamma$, $m,T\ge1$, and the execution (with any permitted demand selection) is of Algorithm 1.
--
--   For every $M\in[0,T-1]$: $R_M$ is finite (each $\bar r(z)$, $z\gg0$, is a finite expectation) and convex on $\mathbb R^m_{++}$, $R_M\ge c^*\ge0$, and $R_M(p^\star)=2W+(M+1)\varepsilon_T\le3W$; for every $\tau>0$, $0<Z_\tau(R_M)<\infty$, and $\|Z\|_1$ and $R_M(Z)$ are integrable under $\pi^{R_M}_\tau$. Moreover, for $2\le t\le T$,
--   $$R_{M_t}(p_t)\le2W+(M_t+1)\,\mathbb E[L_t\mid\mathcal F_{t-1}]\quad\text{a.s.},\tag{53}$$
--   and for every deterministic $y\gg0$,
--   $$\mathbb E\big[e^{[F_{w_t}(y)-R_{M_t}(y)]/W}\big]\le1.\tag{54}$$
--
--   $R_M$ is the deterministic energy that dominates the random history scores in expectation.
--
--   Differences from the source:
--   - encoding: "$R_M$ is finite" → integrability of $\theta\mapsto r_\theta(z)$ under $P$ for every $z\gg0$; reason: $R_M$ is finite exactly when $\bar r(z)$ is a finite expectation
--   - encoding: "Gibbs distributions ... well defined" → $0<Z_\tau(R_M)$; reason: a Bochner normalizer is positive only if it is finite
--   - encoding: the expectation in (54) → a lower Lebesgue integral of the nonnegative integrand over $\Omega$; reason: same value for a nonnegative integrand, and no integrability side condition
--   - encoding: an execution of Algorithm 1 (well defined, measurable and safe by Lemmas 4.1, B.1 and 4.4) → an `Execution` (adapted processes with $q_t\in[0,1]^m$, $p_t\gg0$, $X_t\in D_{\theta_t}(p_t)$ on every path) driven by `alg1 m T W c γ κ`; reason: every execution of Algorithm 1 is such a record, by those lemmas; the records driven by `alg1` are exactly its executions
--   - encoding: rounds $t\in[T]$ → Lean round `k` is the paper round $t=k+1$; the analysis quantities take the paper index $t$; reason: index convention only
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 5.4, (52), (53), (54), p.29 (PDF p.31)

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

/-- **Lemma 5.4 (population energy)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 5.4, (53), (54), p.29 (PDF p.31)). Under
the standing assumptions of Sections 4–6 (p.22, p.27, p.32): an admissible cost `c`; an
i.i.d. buyer model on a standard Borel type space satisfying RC at scale `W > 0` and centered,
`S_θ(1) = 0` (p.18); a comparison price `p⋆` as in (34); `0 < γ ≤ 1` and `κ ≥ 80/γ`; and an
execution (every permitted demand selection) of Algorithm 1 with these `γ, κ`: for every `M ∈ [0, T − 1]`, `R_M` of (52) is finite and convex, `R_M ≥ c* ≥ 0`, and
`R_M(p⋆) = 2W + (M + 1)ε_T ≤ 3W`; its Gibbs distributions at any positive temperature are well
defined, with finite first moments and integrable energy. Moreover, for `2 ≤ t ≤ T`,
`R_{M_t}(p_t) ≤ 2W + (M_t + 1)E[L_t | F_{t−1}]` (53), and for every deterministic `y ≫ 0`,
`E[e^{[F_{w_t}(y) − R_{M_t}(y)]/W}] ≤ 1` (54).

**Formalization Note** "`R_M` is finite" is the integrability of `θ ↦ r_θ(z)` at every `z ≫ 0`
(so that `r̄(z)` is a genuine expectation). Convexity and the bounds are on `ℝ^m_{++}`.
"Well defined" Gibbs distributions means `0 < Z_τ(R_M)` (positive and finite). (53) holds almost
surely; in (54) the expectation of the nonnegative integrand is a lower Lebesgue integral over
`Ω`. -/
theorem lemma_5_4 {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) (W γ κ : ℝ) (hW : 0 < W) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 80 / γ ≤ κ)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0)
    (pstar : Fin m → ℝ) (hpstar : IsComparisonPrice u P c W T pstar)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Execution m T P u μ) (hE : E.DrivenBy (alg1 m T W c γ κ)) :
    (∀ M : ℝ, 0 ≤ M → M ≤ (T : ℝ) - 1 →
      (∀ z ∈ posOrthant m, Integrable (fun θ => surplusRatio u W pstar θ z) P) ∧
      ConvexOn ℝ (posOrthant m) (popEnergy u P c W T pstar M) ∧
      (∀ z ∈ posOrthant m, costConj c z ≤ popEnergy u P c W T pstar M z ∧ 0 ≤ costConj c z) ∧
      popEnergy u P c W T pstar M pstar = 2 * W + (M + 1) * epsT W T ∧
      2 * W + (M + 1) * epsT W T ≤ 3 * W ∧
      ∀ τ : ℝ, 0 < τ →
        0 < gibbsZ τ (popEnergy u P c W T pstar M) ∧
        Integrable (fun z => ∑ i, |z i|) (gibbsMeasure τ (popEnergy u P c W T pstar M)) ∧
        Integrable (popEnergy u P c W T pstar M) (gibbsMeasure τ (popEnergy u P c W T pstar M))) ∧
    (∀ t, 2 ≤ t → t ≤ T →
      (fun ω => popEnergy u P c W T pstar (mass T t) (E.p (t - 1) ω))
        ≤ᵐ[μ] (fun ω => 2 * W + (mass T t + 1) * condExp (E.fil (t - 1)) μ (E.roundLoss c W pstar t) ω) ∧
      ∀ y ∈ posOrthant m,
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((E.surr W c pstar t ω y - popEnergy u P c W T pstar (mass T t) y) / W)) ∂μ
          ≤ 1) := by sorry

end UnobservedWelfare
