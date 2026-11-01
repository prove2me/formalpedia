-- Prove2me | Theorems.Thm_PerfCorrMSQ_eq_5_3
-- name    : PerfCorrMSQ.eq_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:41.747248+00:00
-- url     : https://prove2.me/theorems/19368aa0-dac0-475f-b760-267700e0839c
-- title:
--   Display (5.3) — $(\hat X^n(0),\hat X^n-\hat X^n(0)+\beta_n\eta+\int\hat X^n\wedge0)\Rightarrow(X_0,\sqrt2B)$ (corrected: $+\int_0^\cdot\hat X^n(s)\wedge0\,ds$; joint with the initial condition)
-- statement:
--   Throughout, $\mu=1$, $\theta>0$ is the patience rate, $\lambda_n>0$ is the arrival rate of system $n$, and the systems $n\ge1$ satisfy the model `PerfCorrMSQ.IsModel`: Poisson arrivals, service requirements $S\sim\mathrm{Exp}(1)$ with patience $T=S/\theta$, FIFO service by $n$ servers with abandonment from the queue, and an initial state independent of the fresh draws.
--
--   Assume the staffing rule (1.1) with $\beta\in\mathbb R$ and (Ia) with limit law $\nu$, and let $\beta_n=(n-\lambda_n)/\sqrt n$. Then, as $n\to\infty$,
--
--   $$
--   \Big(\hat X^n(0),\ \hat X^n(\cdot)-\hat X^n(0)+\beta_n\eta(\cdot)+\int_0^\cdot\hat X^n(s)\wedge0\,ds\Big)\Rightarrow\big(X_0,\ \sqrt2B(\cdot)\big)\quad\text{in }D(\mathbb R^2),
--   $$
--
--   where $B$ is a standard Brownian motion and $X_0\sim\nu$ is independent of $B$. Stated in two parts: such $(X_0,B)$ exist on some probability space, and the convergence in distribution holds to every such pair.
--
--   The second coordinate is the noise term of the representation (5.2) after substituting $\hat Z^n=\hat X^n\wedge0$; together with the first it is the input of the continuous map that solves (5.4).
--
--   Differences from the source:
--   - reading: independence of the initial state from the arrivals and the fresh service/patience draws not stated → the initial state (Qⁿ(0), Zⁿ(0), ℓⁿ(0), rⁿ(0)) is independent of the fresh draws, which are mutually independent; the initial state's joint law is otherwise arbitrary; reason: the proofs use it (the time-0 σ-algebra Fⁿ₀ of the martingales, p.11; X₀ independent of B in (1.2)); an initial state that depends on future arrivals keeps X̂ⁿ(0) correlated with the arrival noise and admits no such theorem
--   - reading: §3.3 (p.9) is silent on the patience of the customers waiting at time 0 → an initial waiting customer has remaining patience Exp(θ), independent of everything else, and service requirement θ(ℓ + remaining patience); reason: memorylessness with perfect correlation T = S/θ, as in (2.1); it is the bound hⁿⱼ(t) ≤ θℓⁿᵢ(0) + θ(Tⁿ₀ ∧ t) of p.20 and the abandonment rate θ per waiting customer in (4.1)
--   - reading: (3.8) (p.9) calls rⁿⱼ(t) the "remaining service time" of a customer in phase 1 → rⁿⱼ(0) is the remaining phase-1 time, followed by an independent Exp(1) phase 2, and Lⁿ(0) sums the remaining phase-1 times; reason: §3.3 opens with "remaining phase-1 service time"; the equality on p.11 that counts the customers with rⁿⱼ(t) > 0 and the bound gⁿᵢ(t) ≤ rⁿᵢ(0) on p.20 use this meaning; Lⁿ(0) is then the smaller quantity, so (Ia) and (Ib) are the weaker hypotheses, and this is the stronger reading
--   - encoding: the M/M_pc/n + M_pc system described in words (§2, §3.3) → an explicit FIFO non-idling n-server recursion over customers indexed in queue order (initial waiting customers first, then arrivals); a customer is served iff its service can start strictly before its deadline; counts are Set.ncard; the initial waiting customers are in FIFO order, so their elapsed waits are nonincreasing along the queue; reason: the recursion is the verbal model; the tie rule and the junk value of an infinite count only matter on null events; the order is the page's "ith customer in the queue" under FIFO
--   - encoding: (Ia): (X̂ⁿ(0), L̂ⁿ(0)) ⇒ (X₀, 0) in ℝ² → the laws of X̂ⁿ(0) converge weakly to a probability measure ν, and L̂ⁿ(0) → 0 in probability; reason: the second limit is a constant, so joint convergence in ℝ² is equivalent to the two marginal statements
--   - encoding: sequences indexed by n ≥ 1 → sequences indexed by n : ℕ, model hypotheses for n ≥ 1; reason: at n = 0 every scaled process is the constant 0 (division by √0 = 0), and only the tail of a sequence matters for the limits
--   - correction: X̂ⁿ(·) − X̂ⁿ(0) + βₙη(·) − ∫₀^· X̂ⁿ(s) ∧ 0 ds ⇒ √2B → X̂ⁿ(·) − X̂ⁿ(0) + βₙη(·) + ∫₀^· X̂ⁿ(s) ∧ 0 ds ⇒ √2B; reason: (5.2) reads X̂ⁿ(t) = X̂ⁿ(0) − βₙt − ∫₀ᵗẐⁿ + (terms ⇒ √2B) with Ẑⁿ = X̂ⁿ ∧ 0, which gives +∫; with the printed sign the left side converges to √2B − 2∫₀^·X̂_C ∧ 0, e.g. for X̂ⁿ(0) = −1 (Xⁿ(0) = n − ⌊√n⌋ in service, Lⁿ(0) = 0, so (Ia) holds with ν = δ₋₁) its mean at small t > 0 is about 2t > 0, not 0; the printed sign also contradicts (5.4)
--   - generalization: the second coordinate alone ⇒ √2B → the pair (X̂ⁿ(0), noise) ⇒ (X₀, √2B) jointly, X₀ ∼ ν independent of B; reason: projecting on the second coordinate gives the printed (corrected) statement; the continuous-mapping step after (5.3) needs the joint form, since the solution map of (5.4) also takes x(0)
--   - reading: ⇒ √2B(·) where B is a standard Brownian motion → (i) X₀ ∼ ν and an independent standard Brownian motion B exist on some probability space, and (ii) the convergence holds to every such pair; reason: the statement presupposes the limit exists; a bare 'for every pair' would be vacuous if none existed; both parts together are the stronger reading
--   - encoding: standard Brownian motion → ErlangA.Diffusion.IsStandardBM: Mathlib's IsBrownianReal with every path continuous and every coordinate measurable; reason: every Brownian motion has such a version, and convergence in distribution depends only on the law
--   - encoding: ⇒ in D → PuhaWardFluid.Limit.ConvInDist dist on paths ℝ≥0 → (Fin 2 → ℝ) (J₁, coupling form, one time change for both coordinates); limit objects range over probability spaces in the universe Type; reason: by the Skorokhod representation this is weak convergence in D(ℝ²); every law on path space is carried by such a space
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, proof of Theorem 2*, eq. (5.3), p.13

import Mathlib
import Definitions.Def_PerfCorrMSQ_Scaled
import Definitions.Def_PuhaWardFluid_Limit_Paths
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace PerfCorrMSQ

/-- **Display (5.3)**, proof of Theorem 2* (Yu–Perry, arXiv:2008.12890v1, p.13), corrected and
stated jointly with the initial condition: as `n → ∞`,
`(X̂ⁿ(0), X̂ⁿ(·) − X̂ⁿ(0) + βₙη(·) + ∫₀^· X̂ⁿ(s) ∧ 0 ds) ⇒ (X₀, √2 B(·))` in `D(ℝ²)`,
where `B` is a standard Brownian motion and `X₀ ∼ ν` is independent of `B`.

**Formalization Note.** Hypotheses of §5.1 (p.13): the model with `µ = 1`, `θ > 0`, the
staffing rule (1.1) with any `β ∈ ℝ`, and (Ia).
(correction) The page prints `− ∫₀^· X̂ⁿ(s) ∧ 0 ds`. Substituting `Ẑⁿ = X̂ⁿ ∧ 0` in (5.2),
`X̂ⁿ(t) = X̂ⁿ(0) − βₙt − ∫₀ᵗ Ẑⁿ(s) ds + (terms ⇒ √2 B)`, gives `+ ∫`; the printed sign makes the
left side converge to `√2 B − 2 ∫₀^· X̂_C(s) ∧ 0 ds` instead (e.g. with `ν = δ₋₁`, whose limit
has positive mean at small `t > 0`), and it also contradicts (5.4).
(generalization G3) The printed (5.3) is the second coordinate alone; the joint form implies it
(project) and is what the continuous-mapping step after (5.3) needs, since the solution map of
(5.4) also takes `x(0)`. Stated in two parts: such `(X₀, B)` exist on some probability space,
and the convergence in distribution (`PuhaWardFluid.Limit.ConvInDist`, `J₁`, coupling form)
holds to every such pair. -/
theorem eq_5_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ β : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) (ν : ProbabilityMeasure ℝ) (hθ : 0 < θ) (hmodel : IsModel P θ lam sys)
    (hstaff : StaffingRule lam β) (hIa : InitialIa P θ sys ν) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X₀ : Ω' → ℝ) (B : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' ∧ ErlangA.Diffusion.IsStandardBM P' B ∧ Measurable X₀ ∧
          P'.map X₀ = (ν : Measure ℝ) ∧ IndepFun X₀ (fun ω (t : ℝ≥0) => B t ω) P') ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X₀ : Ω' → ℝ) (B : ℝ≥0 → Ω' → ℝ),
        IsProbabilityMeasure P' → ErlangA.Diffusion.IsStandardBM P' B → Measurable X₀ →
        P'.map X₀ = (ν : Measure ℝ) → IndepFun X₀ (fun ω (t : ℝ≥0) => B t ω) P' →
        PuhaWardFluid.Limit.ConvInDist dist P
          (fun n ω (t : ℝ≥0) => ![Xhat θ sys n ω 0,
            Xhat θ sys n ω t - Xhat θ sys n ω 0 + betaN lam n * t +
              ∫ s in (0 : ℝ)..t, min (Xhat θ sys n ω s) 0]) P'
          (fun ω t => ![X₀ ω, Real.sqrt 2 * B t ω]) := by sorry

end PerfCorrMSQ
