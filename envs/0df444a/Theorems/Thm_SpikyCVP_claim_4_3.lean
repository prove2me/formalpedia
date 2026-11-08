-- Prove2me | Theorems.Thm_SpikyCVP_claim_4_3
-- name    : SpikyCVP.claim_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:49:30.173343+00:00
-- url     : https://prove2.me/theorems/736cb7b0-93cd-4730-a6eb-b8b4d003c3b3
-- title:
--   Claim 4.3 — exponential moment of the gap $\Delta_{j,r}$
-- statement:
--   Let $1<p<2$ and $r>0$. For every $w\in\mathbb R^n$ and every coordinate $j$, with $\Delta_{j,r}$ taken at $u=w_j$,
--
--   $$\mathbb E_{S\sim P_{w,r}}\Big[\exp\Big(\frac{\Delta_{j,r}(S_j)}{2r^p}\Big)\Big]\le 2 .$$
--
--   The paper states it for $w=v^\ast-t$, where $v^\ast$ is a closest vector to $t$. With Markov's inequality it shows that at the optimum the quadratic problem solved in the sampled metric loses at most $8nr^p$ in $\|\cdot\|_p^p$ (Lemma 4.2).
--
--   **Formalization Note** The expectation is a lower Lebesgue integral, so a non-integrable integrand cannot make the bound hold by a default value.
--
--   Differences from the source:
--   - generalization: S ∼ P_{v∗−t,r} and u = v∗_j − t_j, for a closest vector v∗ → S ∼ P_{w,r} and u = w_j for every w ∈ ℝⁿ; reason: the proof uses only the one-dimensional posterior of the j-th coordinate; w = v∗ − t gives the printed claim
--   - encoding: expectation E[exp(Δ_{j,r}(S_j)/(2r^p))] → lower Lebesgue integral ∫⁻ of ENNReal.ofReal of the integrand against postMeasure; reason: the integrand is positive, so the value is the same; no default value for non-integrable functions
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Claim 4.3, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_SpikyCVP_post
import Definitions.Def_SpikyCVP_Ymin

open MeasureTheory

namespace SpikyCVP

/-- **Claim 4.3 (exponential moment of the gap).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Claim 4.3, p.20 (PDF p.22).

Let `p ∈ (1, 2)` and `r > 0`. For every `w ∈ ℝⁿ` and every coordinate `j`,
`E_{S∼P_{w,r}} [exp(∆j,r(S_j)/(2r^p))] ≤ 2`, where `∆j,r` is taken with `u = w_j`.
The paper's case is `w = v∗ − t`, `u = v∗_j − t_j`.

**Formalization Note.** The expectation is a lower Lebesgue integral (`∫⁻`), so a non-integrable
integrand cannot make the bound hold by a junk value. -/
theorem claim_4_3 {n : ℕ} (p r : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hr : 0 < r)
    (w : Fin n → ℝ) (j : Fin n) :
    ∫⁻ s, ENNReal.ofReal (Real.exp (Delta p r (w j) (s j) / (2 * r ^ p))) ∂(postMeasure p w r) ≤ 2 := by sorry

end SpikyCVP
