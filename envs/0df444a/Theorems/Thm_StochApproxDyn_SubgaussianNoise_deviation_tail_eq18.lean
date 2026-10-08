-- Prove2me | Theorems.Thm_StochApproxDyn_SubgaussianNoise_deviation_tail_eq18
-- name    : StochApproxDyn.SubgaussianNoise.deviation_tail_eq18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:53.367547+00:00
-- url     : https://prove2.me/theorems/337c0353-1094-4fc2-9646-ab1b45027cdb
-- title:
--   Eq. (18): $P(\Delta(t,T)\ge\alpha)\le C\exp(-\alpha^2/(C^\prime\int_t^{t+T}\bar\gamma))$
-- statement:
--   Fix the dimension $d$ and a number $\Gamma>0$. There are constants $C>0$ and $C'>0$, depending only on $d$ and $\Gamma$, with the following property. Let $\{x_n\}$ be any Robbins–Monro algorithm $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$ in $\mathbb R^d$, on any probability space, whose noise $\{U_n\}$ is subgaussian with constant $\Gamma$. Let $\bar U$ and $\bar\gamma$ be the piecewise constant processes $\bar U(\tau_n+s)=U_{n+1}$, $\bar\gamma(\tau_n+s)=\gamma_{n+1}$ ($0\le s<\gamma_{n+1}$), and
--   $$\Delta(t,T)=\sup_{0\le h\le T}\Big\|\int_t^{t+h}\bar U(s)\,ds\Big\|.$$
--   Then for all $t\ge0$, $T>0$ and $\alpha>0$,
--   $$P\big(\Delta(t,T)\ge\alpha\big)\le C\exp\Big(\frac{-\alpha^2}{C'\int_t^{t+T}\bar\gamma(s)\,ds}\Big). \tag{18}$$
--
--   Applied at the times $t=kT$, this tail bound together with the hypothesis $\sum_n e^{-c/\gamma_n}<\infty$ makes $\sum_kP(\Delta(kT,T)\ge\alpha)$ finite, so that the Borel–Cantelli lemma gives $\Delta(kT,T)\to0$ almost surely.
--
--   **Formalization Note** $C$ and $C'$ are chosen before the probability space, the step sizes, the noise and $t,T,\alpha$: they depend on $d$ and $\Gamma$ only. $\Delta$ takes values in $[0,\infty]$. The second inequality printed in (18), $\le C\exp(-\alpha^2/(C'T\bar\gamma(u)))$ for some $t\le u\le t+T$, is a mean-value remark and is not part of this statement. If $\int_t^{t+T}\bar\gamma=0$, Lean's division by $0$ makes the right side $C$; in that case every step overlapping $[t,t+T]$ has length $0$, so $\Delta(t,T)=0$ and the left side is $0$ anyway.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.4, p. 17 (PDF p. 18), Eq. (18), first inequality

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.SubgaussianNoise

universe u

/-- Benaïm 1999, §4.2, proof of Proposition 4.4, Eq. (18), first inequality, p. 17: there are
positive constants `C, C'` depending only on the dimension `d` and on `Γ` such that, for every
Robbins–Monro algorithm whose noise is subgaussian with constant `Γ`, and all `t ≥ 0`, `T > 0`,
`α > 0`,
`P(Δ(t, T) ≥ α) ≤ C exp(−α² / (C' ∫_t^{t+T} γ̄(s) ds))`.
`C, C'` are chosen before the probability space, the step sizes, the noise and `t, T, α`. -/
theorem deviation_tail_eq18 (d : ℕ) (Γ : ℝ) (hΓ : 0 < Γ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U → IsSubgaussianWith P ℱ U Γ →
        ∀ t : ℝ, 0 ≤ t → ∀ T : ℝ, 0 < T → ∀ α : ℝ, 0 < α →
          P {ω | ENNReal.ofReal α ≤ StochApproxDyn.MartingaleNoise.noiseDev γ (fun n => U n ω) t T}
            ≤ ENNReal.ofReal (C * Real.exp (-α ^ 2 /
                (C' * ∫ s in t..(t + T), StochApproxDyn.MartingaleNoise.stepPath γ s))) := by sorry

end StochApproxDyn.SubgaussianNoise
