-- Prove2me | Theorems.Thm_OrgAnalytics_proposition_7
-- name    : OrgAnalytics.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:28.755348+00:00
-- url     : https://prove2.me/theorems/0993a2a1-448e-45f3-b27e-7ce9a5ad7023
-- title:
--   Proposition 7, p. 26 — $\lambda^*=1/(2-q_H)$, $\alpha=0$, value $U^*$, $F^*_{opt}$, dual audit (corrected: $\Delta$ in (20), no Assumption 1, ties, $\alpha_H$ of (1))
-- statement:
--   Let $0<\mu<q_H<1$ and $\Delta>0$, and let $U^*=q_H+\mu(1-q_H)/(2-q_H)$. Consider the principal's joint choice of a task allocation $k$, an audit intensity $\lambda$ and a cost distribution $F$.
--
--   1. **Value.** Every designer-optimal outcome of every admissible design gives the principal at most $U^*$.
--   2. **(i)–(ii).** Every optimal design has the prior-independent audit intensity
--   $$
--   \lambda^*=\frac1{2-q_H},
--   $$
--   and the fully informative experiment $\alpha=0$.
--   3. **(iii), optimal policy.** Let $F^*_{opt}$ be the distribution function
--   $$
--   F^*_{opt}(c)=\begin{cases}\alpha_H & c\in\big[0,\ \tfrac{(1-q_H)\Delta}{2-q_H}\big),\\[2pt] 1 & c\ge\tfrac{(1-q_H)\Delta}{2-q_H}.\end{cases}
--   $$
--   It is a cost distribution, and for each $k\in\{I,S\}$ there is an optimal design $(k,\lambda^*,F^*_{opt},o)$ with $\alpha=0$, utility $U^*$ and zero expected tampering cost, which is the least expected tampering cost among all optimal designs. So the principal is indifferent between separating and integrating tasks.
--   4. **(iii), multiplicity.** Some other cost distribution, satisfying Assumption 1 at $\lambda^*$, is also optimal at $\lambda^*$ for each $k$.
--   5. **(iv), dual audit.** With costless tampering, an internal audit that rectifies a tampered report with probability $(q_H-\mu)/(q_H(1-\mu))$ and an external audit of intensity $\lambda^*$, the designer has an optimal outcome with $\alpha=0$, in which tampering succeeds with probability $\alpha_H$, the mass of $F^*_{opt}$ at cost $0$, and the principal gets $U^*$.
--
--   This is the paper's main result on data governance: an imperfect audit and a fallible prevention system together induce the designer to reveal the state.
--
--   Differences from the source:
--   - correction: (1) prints α_H with denominator q_H(1−q_H), a product → α_H = µ(1−q_H)/((1−µ)q_H), the denominator being the odds q_H/(1−q_H); reason: counterexample: at µ = 1/4, q_H = 3/8 the printed form is 64/45 > 1, not a probability; the sentence before (1) sets the posterior to q_H, which solves to the Lean value, and (2) needs it
--   - correction: (20) has the cut-off (1−q_H)/(2−q_H) → the cut-off of F*_opt is (1−q_H)Δ/(2−q_H); reason: counterexample: µ = 1/4, q_H = 3/8, Δ = 2, λ = 8/13 with (20) as printed: at α = 0 every agent tampers once τ > 1/2, the designer picks the commitment experiment and the principal gets q_H = 0.375 < U* ≈ 0.471; the proof on p. 48 has c̃ = (1−λ_opt)Δ
--   - correction: Assumption 1 restricts data policies throughout (p. 13) → admissible designs are all cost distributions on [0, ∞) with λ ∈ [0, 1]; reason: F*_opt has no mass above (1−λ*)Δ, so it violates Assumption 1; the value bound over all distributions implies the one over the class, and clause 4 gives an optimal policy inside the class
--   - correction: each π_S(α) has "the unique continuation equilibrium", given by (6)–(7) (p. 14) → IsContEq allows every continuation equilibrium, with ties F_<(g) ≤ t ≤ F_≤(g) and free mixing at posterior q_H, and the designer selects one; reason: counterexample: µ = 1/4, q_H = 3/8, Δ = 1, λ = 8/13, F = F*_opt, α = 0: every τ ∈ (0, 1] with t = 5/9 is a continuation equilibrium; with atoms (6) may also have no solution
--   - reading: the optimal design of {k, λ, F}, with the designer indifferent at the optimum between α = 0 and α_H → IsOptimalDesign maximizes U over pairs of a design and a designer-optimal outcome, so designer ties go to the principal; reason: the incentive constraint (A.7) binds at the optimum; with ties against her the supremum is not attained, and the proof of Proposition 6 uses the weak inequality
--   - reading: F*_opt "minimizes expected tampering costs" and "the principal is indifferent between separating and integrating tasks" → ETC = 0, which is at most the ETC of every optimal design, and an optimal design with value U* exists for each k; reason: the proof says the distribution induces zero costs, so both allocations select the same experiment
--   - reading: "the principal can implement (20) through a dual internal-external audit" → a designer-optimal outcome of the dual game has α = 0, effective tampering probability α_H and utility U*; reason: this reproduces the on-path behaviour and value of F*_opt; the paper gives no further definition of implementation
--   - reading: the designer picks any finite experiment and play is weak perfect Bayesian (pp. 9, 12) → the designer picks a status-quo experiment π_S(α); reason: the paper poses the organizational-design problem over status-quo experiments after Proposition 2 (p. 15), and its proofs of Propositions 6 and 7 work there; Propositions 1–2 are not modelled
--   - generalization: α ranges over the set A of (5) → α ranges over [0, 1]; reason: A ⊆ [0, 1]; an α outside A has only continuations the designer strictly improves on or that pay 0, so the designer maximum is the one over A
--   - reading: reporting and decisions off the tampering margin are equilibrium play in (7) and footnote 18 → after s = H the agent reports H; the principal keeps d_S after an audited s = S and after an unaudited m = S; these are fixed in Outcome; reason: (7) and footnote 18 state this play for status-quo experiments; fixing it removes the off-path beliefs Assumption 1 was introduced to tie down
--   - reading: a common prior µ with µ < q_H (p. 9) → 0 < µ < q_H < 1; reason: at µ = 0, α_H = 0 and every λ gives q_H, so the optimal audit is not pinned down; µ > 0 also makes every posterior well defined
--   - encoding: a distribution function F of the cost c, on [0, ∞) → a probability measure on ℝ with no mass below 0; F(c) is massLE F c; reason: same objects; atoms are kept, as the paper needs them
-- source:
--   Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), doi:10.1287/mnsc.2023.00207, Proposition 7, eqs. (19)–(20), p.26 (PDF 28); discussion pp.26–27 (PDF 28–29); proof p.48 (PDF 50)

import Mathlib
import Definitions.Def_OrgAnalytics_Model

open MeasureTheory

namespace OrgAnalytics

/-- **Proposition 7: optimal data governance.** The principal's value over all designs is
`U* = q_H + µ(1 − q_H)/(2 − q_H)`, and:
* (i)–(ii) every optimal design has the prior-independent audit intensity `λ = 1/(2 − q_H)` and
  the fully informative experiment `α = 0`;
* (iii) `F*_opt` is an optimal policy under integration and under separation, so the principal is
  indifferent between them; it has zero expected tampering cost, the least among optimal designs;
* (iii) it is not the only optimal policy: another one, satisfying Assumption 1, is optimal under
  both task allocations;
* (iv) the dual internal–external audit, with costless tampering and internal audit success
  `(q_H − µ)/(q_H(1 − µ))`, reproduces the tampering rate `α_H` of the cost-`0` atom of `F*_opt`
  and attains `U*`.

Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), Proposition 7,
eqs. (19)–(20), p.26 (PDF 28); proof, p.48 (PDF 50).

**Formalization Note** The optimal design problem is posed over status-quo experiments, as the
paper does after Proposition 2. Designer ties are broken for the principal; see
`Params.IsOptimalDesign`. `F*_opt` has the cut-off `(1 − q_H) Δ/(2 − q_H)`; see `Params.Fopt`. -/
theorem proposition_7 (P : Params) :
    (∀ (k : TaskAlloc) (lam : ℝ) (F : Measure ℝ) (o : Outcome), Admissible lam F →
      P.IsDesignerOpt k lam F o → P.principalUtility lam o ≤ P.UStar) ∧
    (∀ (k : TaskAlloc) (lam : ℝ) (F : Measure ℝ) (o : Outcome), P.IsOptimalDesign k lam F o →
      lam = 1 / (2 - P.qH) ∧ o.α = 0) ∧
    (IsCostDist P.Fopt ∧
      ∀ k : TaskAlloc, ∃ o, P.IsOptimalDesign k P.lamStar P.Fopt o ∧ o.α = 0 ∧
        P.principalUtility P.lamStar o = P.UStar ∧
        P.tamperingCost P.lamStar P.Fopt o = 0 ∧
        ∀ (k' : TaskAlloc) (lam' : ℝ) (F' : Measure ℝ) (o' : Outcome),
          P.IsOptimalDesign k' lam' F' o' →
            P.tamperingCost P.lamStar P.Fopt o ≤ P.tamperingCost lam' F' o') ∧
    (∃ F : Measure ℝ, F ≠ P.Fopt ∧ P.AssumptionOne P.lamStar F ∧
      ∀ k : TaskAlloc, ∃ o, P.IsOptimalDesign k P.lamStar F o) ∧
    (∃ o, P.IsDualDesignerOpt P.lamStar P.rStar o ∧ o.α = 0 ∧
      (o.effective P.rStar).t = P.alphaH ∧
      P.principalUtility P.lamStar (o.effective P.rStar) = P.UStar) := by sorry

end OrgAnalytics
