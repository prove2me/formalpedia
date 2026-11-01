-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_tight_instance
-- name    : SingleFactorPricing.LogBound.tight_instance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:14.171859+00:00
-- url     : https://prove2.me/theorems/6f4f28a6-d082-41b8-b078-47c8ee37d158
-- title:
--   Proof of Theorem 1, p.4 — the tight instance: $\bar{\mathcal R}=1$, $\mathcal R^e=1/\beta$
-- statement:
--   Let $\rho>1$, $\beta=1+\ln\rho$ and $k=1/\beta$. Take one product, $f=1$, and the probability law $\mu$ on $[1,\rho]$ with density $v^{-2}$ on $(1,\rho)$ and an atom of mass $1/\rho$ at $\rho$. A type $v$ demands $k\mathbf 1\{p\le v\}$ and is priced at $\bar p_v=v$. Then:
--
--   1. $\mu$ is a probability measure;
--   2. the aggregate demand is $k$ at $p=0$ and $k\min(1,1/p)$ for $0<p\le\rho$;
--   3. every hypothesis of Theorem 1 holds, with $q_{\min}=1$, $q_{\max}=\rho$ and $\mathcal R^e=1/\beta$;
--   4. A1 holds as an equality: $G(q)=H(q)$ for all $q\ge0$;
--   5. $\bar{\mathcal R}=1$;
--   6. every $q\in[1,\rho]$ attains $R(q)=1/\beta$.
--
--   Hence $\bar{\mathcal R}/\mathcal R^e=\beta=1+\ln\rho$, the exact tightness of Theorem 1.
--
--   Differences from the source:
--   - reading: the tail $d(p)=k\min(1,1/p)$ called the distribution of types; it has total mass $k$, against $\sum_j\theta_j=1$ of §2, and "integrates to one" refers to $\int_0^\rho d(p)\,dp=1$ → a probability law on $[1,\rho]$ with tail $\min(1,1/p)$, each type demanding $k$ units; reason: the aggregate demand, $\bar{\mathcal R}$ and $\mathcal R^e$ are the paper's, and the model of §2 is respected
--   - reading: $d(p)=k\min(1,1/p)$ over $p\in[0,\rho]$ → $p=0$ stated separately, with value $k$; reason: $1/0=0$ in Lean; the paper means $\min(1,1/p)=1$ at $p=0$
--   - encoding: a continuum of types in $[1,\rho]$ → the subtype `Set.Icc 1 ρ`; reason: A0 and optimality must hold at every type, which fails for $v\le0$
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, proof of Theorem 1, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_aggregateProfit
import Definitions.Def_SingleFactorPricing_LogBound_personalizedProfit
import Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
import Definitions.Def_SingleFactorPricing_LogBound_factorDemand
import Definitions.Def_SingleFactorPricing_LogBound_LogBoundInstance
import Definitions.Def_SingleFactorPricing_LogBound_tailLaw
import Definitions.Def_SingleFactorPricing_LogBound_tightDemand
import Definitions.Def_SingleFactorPricing_LogBound_tightPrice

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **M6: the tight instance.** Gallego, Berbeglia, arXiv:2102.03038v2, proof of Theorem 1, p.4:
"Suppose there are a continuum of types with willingness to pay in the interval `[1, ρ]` for some
`ρ > 1`. Assume that tail of the distribution of types is given by `d(p) = k min(1, 1/p)` over
`p ∈ [0, ρ]` with `k = 1/β` and `β = 1 + ln(ρ)`, so that it integrates to one. Then, personalized
pricing results in expected profit 1, so `R̄ = 1`. For uniform pricing, any price in the interval
`[1, ρ]` is optimal, resulting in expected profit `Rᵉ = 1/β`. Clearly `R̄/Rᵉ = β = 1 + ln(ρ)` so the
bound is tight."

**Formalization Note.** One product, `f = e = 1`. The type space is `[1, ρ]` with the probability
law `tailLaw ρ`, and each type demands `k` units up to its willingness to pay. The aggregate demand
equals the paper's `d(p)`; since `1/0 = 0` in Lean, `p = 0` is stated separately, with the value
`k` that the paper's `k min(1, 1/p)` has there. `LogBoundInstance … 1 ρ (1/β)` records every
hypothesis of Theorem 1, `q_min = 1`, `q_max = ρ` and `Rᵉ = 1/β`. -/
theorem tight_instance (ρ : ℝ) (hρ : 1 < ρ) :
    IsProbabilityMeasure (tailLaw ρ) ∧
      (∫ v, tightDemand ρ v (fun _ => 0) 0 ∂tailLaw ρ = 1 / (1 + Real.log ρ)) ∧
      (∀ p ∈ Set.Ioc (0 : ℝ) ρ, ∫ v, tightDemand ρ v (fun _ => p) 0 ∂tailLaw ρ =
        1 / (1 + Real.log ρ) * min 1 (1 / p)) ∧
      LogBoundInstance (tailLaw ρ) (tightDemand ρ) (fun _ => 1) (tightPrice ρ) 1 ρ
        (1 / (1 + Real.log ρ)) ∧
      (∀ q : ℝ, 0 ≤ q → filteredDemand (tailLaw ρ) (tightDemand ρ) (fun _ => 1) (tightPrice ρ) q =
        factorDemand (tailLaw ρ) (tightDemand ρ) (fun _ => 1) q) ∧
      personalizedProfit (tailLaw ρ) (tightDemand ρ) (tightPrice ρ) = 1 ∧
      ∀ q ∈ Set.Icc (1 : ℝ) ρ, aggregateProfit (tailLaw ρ) (tightDemand ρ) (q • fun _ => 1) =
        1 / (1 + Real.log ρ) := by sorry

end SingleFactorPricing.LogBound
