-- Prove2me | Theorems.Thm_StochApproxDyn_MartingaleNoise_moment_bound_eq16
-- name    : StochApproxDyn.MartingaleNoise.moment_bound_eq16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:28:10.791446+00:00
-- url     : https://prove2.me/theorems/cbdc60ad-093a-4a2a-af41-ff14a773e9f8
-- title:
--   Eq. (16): $E(\Delta(t,T)^q)\le C(q,T)\int_t^{t+T}\bar\gamma^{q/2}(s)\,ds$
-- statement:
--   Let $\{x_n\}$, given by (7), be a Robbins–Monro algorithm with noise $\{U_n\}$ in $\mathbb R^d$ and step sequence $\{\gamma_n\}$, and suppose that for some $q\ge2$
--   $$\sup_n E\big(\|U_{n+1}\|^q\big)<\infty .$$
--   Then for every $T>0$ there is a constant $C(q,T)>0$ such that for all $t\ge0$
--   $$E\big(\Delta(t,T)^q\big)\le C(q,T)\int_t^{t+T}\bar\gamma^{q/2}(s)\,ds, \tag{16}$$
--   where $\Delta(t,T)=\sup_{0\le h\le T}\|\int_t^{t+h}\bar U(s)\,ds\|$ is the noise deviation (10) of the realised noise path and $\bar\gamma$ is the step-size process.
--
--   This moment bound on the noise deviation over a window of length $T$ is what makes the windows $[kT,(k+1)T]$ summable in Eq. (17).
--
--   **Formalization Note** The moment hypothesis is a bound $\int\|U_{n+1}\|^q\,dP\le M$ with $M<\infty$ on integrals in $[0,\infty]$, and $E(\Delta(t,T)^q)$ is also an integral in $[0,\infty]$, so no default value of a non-integrable expectation enters. The constant $C(q,T)$ may depend on $q$, $T$, the dimension, the moment bound and the step sequence, but not on $t$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.2, p. 15 (PDF p. 16), Eq. (16)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, Eq. (16), p. 15: for a Robbins–Monro algorithm
with `q ≥ 2` and `sup_n E‖U_{n+1}‖^q < ∞`, for every `T > 0` there is `C(q, T) > 0` (independent
of `t`) with `E(Δ(t, T)^q) ≤ C(q, T) ∫_t^{t+T} γ̄(s)^{q/2} ds` for all `t ≥ 0`. -/
theorem moment_bound_eq16 {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (q : ℝ) (hq : 2 ≤ q)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n : ℕ, ∫⁻ ω, ‖U (n + 1) ω‖ₑ ^ q ∂P ≤ M) :
    ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, noiseDev γ (fun n => U n ω) t T ^ q ∂P ≤
        ENNReal.ofReal C * ∫⁻ s in Set.Icc t (t + T), ENNReal.ofReal (stepPath γ s ^ (q / 2)) := by sorry

end StochApproxDyn.MartingaleNoise
