-- Prove2me | Theorems.Thm_PrivLearn_SQSim_iteration_analysis
-- name    : PrivLearn.SQSim.iteration_analysis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:16.795392+00:00
-- url     : https://prove2.me/theorems/e9a1338d-6f2b-407e-8846-f7aeeb0410ca
-- title:
--   Proof of Claim 5.9, p. 23 — one rejection-sampling iteration terminates with probability ≥ ((1−φ)/(1+φ))e^{−ε} and outputs w with conditional probability in (1 ± 3φ)p(w)
-- statement:
--   Let $P$, $R$ (an $\varepsilon$-local randomizer with discrete output, $\varepsilon>0$), $u_0$, $q(w)=\Pr[R(u_0)=w]$ and $p(w)=\mathbb E_{u\sim P}\Pr[R(u)=w]$ be as in display (5), and let $0<\beta\le1$, $t\ge1$ and $\varphi=\beta/(3t)$. Let $\tilde p:W\to\mathbb R$ be any function with
--
--   $$|\tilde p(w)-p(w)|\le\varphi\,p(w)\qquad\text{whenever }q(w)>0 .$$
--
--   One iteration of $\mathcal B_{R,\varepsilon}$ samples $w\sim q$ and outputs it with probability $\mathrm{acc}(w)=\tilde p(w)/\bigl(q(w)(1+\varphi)e^{\varepsilon}\bigr)$. Then:
--
--   1. $0\le\mathrm{acc}(w)\le1$ for every $w$ with $q(w)>0$;
--   2. the termination probability $p_{\mathrm{terminate}}=\sum_w q(w)\,\mathrm{acc}(w)$ satisfies
--
--   $$\frac{1-\varphi}{1+\varphi}\,e^{-\varepsilon}\le p_{\mathrm{terminate}}\le e^{-\varepsilon};$$
--
--   3. conditioned on termination, $w$ is output with probability in $(1\pm3\varphi)p(w)$:
--
--   $$\Bigl|\frac{q(w)\,\mathrm{acc}(w)}{p_{\mathrm{terminate}}}-p(w)\Bigr|\le3\varphi\,p(w)\qquad\text{for every }w .$$
--
--   The estimate $\tilde p$ may change from iteration to iteration with the oracle's answers; the statement holds for each fixed iteration, which is how the paper bounds the output law and the expected number of iterations of $\mathcal B_{R,\varepsilon}$.
--
--   **Formalization Note.** The upper bound $e^{-\varepsilon}$ is the paper's $(1+\varphi)/((1+\varphi)e^{\varepsilon})$. For $w$ with $q(w)=0$ the algorithm never samples $w$; Lean's $x/0=0$ gives $\mathrm{acc}(w)=0$ there, and $p(w)=0$ by locality, so the statements hold at such $w$ too. The paper's derived bound on the expected number of iterations, $\frac{1+\varphi}{1-\varphi}e^{\varepsilon}\le2e^{\varepsilon}$, is the reciprocal of item 2 and enters Claim 5.9.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 23, proof of Claim 5.9 (paragraphs "Nevertheless, p̃ is fixed …" and "Moreover, since each iteration terminates …")

import Mathlib
import Definitions.Def_PrivLearn_SQSim_LocalAlg
import Definitions.Def_PrivLearn_SQSim_Estimate

open MeasureTheory

namespace PrivLearn.SQSim

/-- Proof of Claim 5.9 (p. 23): one iteration of `B_{R,ε}`. Let `p̃ : W → ℝ` be any estimate
satisfying (5) at every `w` with `q(w) = Pr[R(u₀) = w] > 0` (it may depend on the iteration).
The iteration samples `w ∼ q` and outputs it with probability
`acc(w) = p̃(w) / (q(w)(1 + φ)e^ε)`. Then every `acc(w)` is a probability, the iteration terminates
with probability `p_terminate = Σ_w q(w) acc(w)` between `((1 − φ)/(1 + φ)) e^{−ε}` and `e^{−ε}`,
and, conditioned on terminating, it outputs `w` with probability in `(1 ± 3φ) p(w)`. -/
theorem iteration_analysis {Dom W : Type*} [MeasurableSpace Dom] (P : Measure Dom)
    [IsProbabilityMeasure P] (R : Dom → PMF W) (hmeas : ∀ w, Measurable fun u => R u w)
    (u₀ : Dom) (ε β : ℝ) (t : ℕ) (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (ht : 1 ≤ t)
    (hR : IsLocalRandomizerPMF R ε) (pt : W → ℝ)
    (hpt : ∀ w, 0 < R u₀ w → |pt w - pTarget P R w| ≤ simPhi β t * pTarget P R w) :
    let φ : ℝ := simPhi β t
    let acc : W → ℝ := fun w => pt w / ((R u₀ w).toReal * (1 + φ) * Real.exp ε)
    let pTerm : ℝ := ∑' w, (R u₀ w).toReal * acc w
    (∀ w, 0 < R u₀ w → 0 ≤ acc w ∧ acc w ≤ 1) ∧
    (1 - φ) / (1 + φ) * Real.exp (-ε) ≤ pTerm ∧ pTerm ≤ Real.exp (-ε) ∧
    ∀ w, |(R u₀ w).toReal * acc w / pTerm - pTarget P R w| ≤ 3 * φ * pTarget P R w := by sorry

end PrivLearn.SQSim
