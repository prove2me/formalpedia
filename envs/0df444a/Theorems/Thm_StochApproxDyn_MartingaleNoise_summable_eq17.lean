-- Prove2me | Theorems.Thm_StochApproxDyn_MartingaleNoise_summable_eq17
-- name    : StochApproxDyn.MartingaleNoise.summable_eq17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:28:39.409624+00:00
-- url     : https://prove2.me/theorems/af9e34c7-315f-4a96-b58e-9928446306c2
-- title:
--   Eq. (17): $\sum_{k\ge0}E(\Delta(kT,T)^q)<\infty$
-- statement:
--   Let $\{x_n\}$, given by (7), be a Robbins–Monro algorithm with noise $\{U_n\}$ in $\mathbb R^d$ and step sequence $\{\gamma_n\}$. Suppose that for some $q\ge2$
--   $$\sup_n E\big(\|U_{n+1}\|^q\big)<\infty\qquad\text{and}\qquad\sum_n\gamma_n^{1+q/2}<\infty .$$
--   Then for every $T>0$
--   $$\sum_{k\ge0}E\big(\Delta(kT,T)^q\big)<\infty, \tag{17}$$
--   where $\Delta(t,T)$ is the noise deviation (10) of the realised noise path.
--
--   By the Borel–Cantelli lemma this gives $\Delta(kT,T)\to0$ almost surely as $k\to\infty$.
--
--   **Formalization Note** The paper prints the chain $\sum_k E(\Delta(kT,T)^q)\le C(q,T)\int_0^\infty\bar\gamma^{q/2}(s)\,ds=\sum\gamma_{i+1}^{1+q/2}<\infty$, whose middle equality drops the factor $C(q,T)$; only the finiteness is formalized. Expectations are integrals in $[0,\infty]$ and the sum is the sum in $[0,\infty]$; the summability of $\gamma_{n+1}^{1+q/2}$ is real summability of a nonnegative sequence.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.2, p. 16 (PDF p. 17), Eq. (17)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, Eq. (17), p. 16: under the hypotheses of
Proposition 4.2, for every `T > 0`, `∑_{k ≥ 0} E(Δ(kT, T)^q) < ∞`. -/
theorem summable_eq17 {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (q : ℝ) (hq : 2 ≤ q)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n : ℕ, ∫⁻ ω, ‖U (n + 1) ω‖ₑ ^ q ∂P ≤ M)
    (hsum : Summable (fun n : ℕ => γ (n + 1) ^ (1 + q / 2))) :
    ∀ T : ℝ, 0 < T →
      ∑' k : ℕ, ∫⁻ ω, noiseDev γ (fun n => U n ω) ((k : ℝ) * T) T ^ q ∂P < ⊤ := by sorry

end StochApproxDyn.MartingaleNoise
