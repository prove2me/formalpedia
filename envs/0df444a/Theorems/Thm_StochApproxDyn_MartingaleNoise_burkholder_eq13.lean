-- Prove2me | Theorems.Thm_StochApproxDyn_MartingaleNoise_burkholder_eq13
-- name    : StochApproxDyn.MartingaleNoise.burkholder_eq13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:27:48.253849+00:00
-- url     : https://prove2.me/theorems/1f67b176-f83b-4034-83de-2e1c40cf679b
-- title:
--   Eq. (13): Burkholder's inequality for the noise sums of a Robbins–Monro algorithm
-- statement:
--   Fix a dimension $d$ and an exponent $q\ge2$. There is a constant $C_q>0$, depending only on $q$ and $d$, with the following property. Let $\{x_n\}$, given by (7), be a Robbins–Monro algorithm on a probability space $(\Omega,\mathcal F,P)$ with filtration $\{\mathcal F_n\}$, step sequence $\{\gamma_n\}$ and noise $\{U_n\}$ in $\mathbb R^d$, with times $\tau_n$ and inverse $m(t)$. Then for every $n\ge0$ and every $T>0$
--   $$E\Big\{\sup_{n<k\le m(\tau_n+T)}\Big\|\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}\Big\|^q\Big\}\le C_q\,E\Big\{\Big[\sum_{i=n}^{m(\tau_n+T)-1}\gamma_{i+1}^2\|U_{i+1}\|^2\Big]^{q/2}\Big\}. \tag{13}$$
--
--   This is the instance of Burkholder's martingale inequality used in the proof of Proposition 4.2: the partial sums $\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}$ form a martingale in $k$, and the right-hand side is the $q/2$-th moment of its square function.
--
--   **Formalization Note** Both expectations are integrals in $[0,\infty]$ (either side may be $+\infty$). The supremum over an empty range ($m(\tau_n+T)\le n$) is $0$. The constant $C_q$ is chosen before the probability space, the algorithm, $n$ and $T$, so it is universal. The paper writes "for any $t\ge0$" before (13); the statement is about the index $n$ and the window length $T$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.2, p. 15 (PDF p. 16), Eq. (13)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

universe u

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, Eq. (13), p. 15: the instance of Burkholder's
inequality used in the proof. For `q ≥ 2` there is a constant `C_q > 0` (depending only on `q`
and the dimension `d`) such that for every Robbins–Monro algorithm, every `n` and every `T > 0`,
`E sup_{n<k≤m(τ_n+T)} ‖∑_{i=n}^{k-1} γ_{i+1}U_{i+1}‖^q ≤ C_q E[(∑_{i=n}^{m(τ_n+T)-1} γ_{i+1}² ‖U_{i+1}‖²)^{q/2}]`. -/
theorem burkholder_eq13 (d : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        IsRobbinsMonro P ℱ F γ x U →
        ∀ (n : ℕ) (T : ℝ), 0 < T →
          ∫⁻ ω, (Finset.Ioc n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T))).sup
              (fun k => ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω‖ₑ ^ q) ∂P
            ≤ ENNReal.ofReal C *
              ∫⁻ ω, (∑ i ∈ Finset.Ico n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
                  ENNReal.ofReal (γ (i + 1) ^ 2) * ‖U (i + 1) ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P := by sorry

end StochApproxDyn.MartingaleNoise
