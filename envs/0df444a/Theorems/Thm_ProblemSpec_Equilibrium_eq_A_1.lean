-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_eq_A_1
-- name    : ProblemSpec.Equilibrium.eq_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:31.439037+00:00
-- url     : https://prove2.me/theorems/b7d122b9-a846-4631-8837-9367b5f72e44
-- title:
--   (A.1), App. p. 1 — Gumbel trial shocks give the logit win probability
-- statement:
--   Let $N\ge2$ designers take part. Designer $i$ generates $m_i\ge1$ design trials of baseline quality $v(r_i)$, and each of the other $N-1$ designers generates $m\ge1$ trials of baseline quality $v(r)$, where $v$ is the baseline quality of (2). The quality of each trial is its baseline quality plus a shock, and the $m_i+(N-1)m$ shocks are independent, each with the zero-mean Gumbel law of scale $\mu$ (distribution function $F(x)=\exp(-\exp(-(x/\mu+\gamma)))$, $\gamma$ Euler's constant).
--
--   Then the probability that designer $i$'s best trial is strictly better than every opponent's best trial is
--   $$\Pr(i\text{ wins})=\frac{m_i\,e^{v(r_i)/\mu}}{m_i\,e^{v(r_i)/\mu}+(N-1)\,m\,e^{v(r)/\mu}}.$$
--
--   This is the only link between the stochastic contest and the logit formula (A.1) on which all later results rest.
--
--   **Formalization Note** The shocks are the coordinates of the product measure $G^{\otimes(m_i+(N-1)m)}$ on the index set $\{1,\dots,m_i\}\sqcup(\{1,\dots,N-1\}\times\{1,\dots,m\})$, where $G$ is the zero-mean Gumbel law with scale $\mu$ of the published definition `AssortSearch.Cannibal.Model`. "Best trial of $i$ beats every opponent's best trial" is written as: some trial $\tau$ of $i$ beats every opponent trial. The trial counts are natural numbers here; elsewhere the mission uses (A.1) for real $m_i,m$, as the paper does.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), (A.1); shocks p. 8 (PDF 8)

import Mathlib
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_ProblemSpec_Equilibrium_Model
open MeasureTheory

namespace ProblemSpec.Equilibrium

/-- (A.1), App. p. 1 (PDF 29). Designer `i` generates `mi ≥ 1` trials of baseline quality
`v(ri)`, each of the other `N − 1 ≥ 1` designers generates `m ≥ 1` trials of baseline quality
`v(r)`, and the trial shocks are i.i.d. zero-mean Gumbel with scale `μ` (index `Sum.inl τ`:
`i`'s trial `τ`; `Sum.inr (j, τ)`: opponent `j`'s trial `τ`). The probability that `i`'s best
trial strictly beats every opponent's best trial is
`mi e^{v(ri)/μ} / (mi e^{v(ri)/μ} + (N − 1) m e^{v(r)/μ})`. -/
theorem eq_A_1 (P : Params) (hP : P.Standing) (Sr ri r : ℝ) (N mi m : ℕ)
    (hN : 2 ≤ N) (hmi : 1 ≤ mi) (hm : 1 ≤ m)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : AssortSearch.Cannibal.IsZeroMeanGumbel P.μ G) :
    (Measure.pi (fun _ : Fin mi ⊕ (Fin (N - 1) × Fin m) => G)
        {ε | ∃ τ : Fin mi, ∀ k : Fin (N - 1) × Fin m,
          quality P Sr r + ε (Sum.inr k) < quality P Sr ri + ε (Sum.inl τ)}).toReal
      = winProb P Sr (N : ℝ) ri (mi : ℝ) r (m : ℝ) := by sorry

end ProblemSpec.Equilibrium
