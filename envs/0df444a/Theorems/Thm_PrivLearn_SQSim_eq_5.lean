-- Prove2me | Theorems.Thm_PrivLearn_SQSim_eq_5
-- name    : PrivLearn.SQSim.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:21.077985+00:00
-- url     : https://prove2.me/theorems/7e612dfd-149d-4706-9b89-7de58237be2c
-- title:
--   Display (5) — the SQ estimate p̃(w) lies in (1 ± φ)p(w), φ = β/(3t), and the query g is [−1, 1]-valued
-- statement:
--   Let $P$ be a probability distribution on $D$, let $R$ be an $\varepsilon$-local randomizer with discrete output set $W$ ($\varepsilon>0$), with $u\mapsto\Pr[R(u)=w]$ measurable, and let $u_0\in D$. Fix $\beta>0$, an integer $t\ge1$, and an output $w$ with $q(w)=\Pr[R(u_0)=w]>0$. Let
--
--   $$g(u)=\frac{\Pr[R(u)=w]-q(w)}{q(w)(e^{\varepsilon}-e^{-\varepsilon})},\qquad \tau=\frac{\beta}{3e^{2\varepsilon}t},\qquad p(w)=\mathbb E_{u\sim P}\Pr[R(u)=w].$$
--
--   Then $g(u)\in[-1,1]$ for every $u$, and for every valid answer $v$ of the SQ oracle to $(g,\tau)$, that is, every $v$ with $|v-\mathbb E_{u\sim P}[g(u)]|\le\tau$, the estimate $\tilde p(w)=v\,q(w)(e^{\varepsilon}-e^{-\varepsilon})+q(w)$ satisfies
--
--   $$\tilde p(w)\in(1\pm\varphi)\,p(w),\qquad \varphi=\frac{\beta}{3t}.$$
--
--   This is the accuracy guarantee of Steps 2 and 3 of the simulation algorithm $\mathcal B_{R,\varepsilon}$; it holds for every valid answer, so the oracle may be adversarial.
--
--   **Formalization Note.** The inclusion is stated as $|\tilde p(w)-p(w)|\le\varphi\,p(w)$. The paper's input $\mathbf 0$ is an arbitrary $u_0$. The paper's standing $\beta\le1$ is not needed here and is not assumed.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 22, proof of Claim 5.9, display (5), proved on p. 23 (including "g(z_i) ∈ [−1, 1] for all z_i")

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open MeasureTheory

namespace PrivLearn.SQSim

/-- Display (5) (p. 22, proved on p. 23): for an ε-local randomizer `R` with discrete output, a
reference input `u₀` and an output `w` with `q(w) = Pr[R(u₀) = w] > 0`, the query `g` of Step 2
takes values in `[−1, 1]`, and for every valid answer `v` of the SQ oracle to `(g, τ)` with
`τ = β/(3e^{2ε}t)` the estimate `p̃(w)` of Step 3 satisfies `p̃(w) ∈ (1 ± φ) p(w)`, `φ = β/(3t)`. -/
theorem eq_5 {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom) [IsProbabilityMeasure P]
    (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w) (u₀ : Dom) (ε β : ℝ) (t : ℕ)
    (hε : 0 < ε) (hβ : 0 < β) (ht : 1 ≤ t) (hR : IsLocalRandomizerPMF R ε)
    (w : W) (hq : 0 < R u₀ w) (v : ℝ)
    (hv : IsSQAnswer P (sqQuery (fun u => (R u w).toReal) u₀ ε) (simTolerance ε β t) v) :
    (∀ u, sqQuery (fun u => (R u w).toReal) u₀ ε u ∈ Set.Icc (-1 : ℝ) 1) ∧
    |sqEstimate (fun u => (R u w).toReal) u₀ ε v - pTarget P R w| ≤
      simPhi β t * pTarget P R w := by sorry

end PrivLearn.SQSim
