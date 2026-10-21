-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_proposition_1
-- name    : ToneAtTop.Diversion.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:07.660006+00:00
-- url     : https://prove2.me/theorems/e3b3eea8-256f-4f39-8aeb-afa3f631f1a3
-- title:
--   Proposition 1, pp. 11–12 — optimal control and high-type tipping point
-- statement:
--   Let the diversion model satisfy its standing assumptions, and suppose the two conditions of Lemma 1 hold: $\tau<\sqrt{2\lambda\bar x/p}$ and $p>1-2\lambda\bar x/\tau^2$. Put $q=\sqrt{2\lambda\bar x/(1+p)}$. The authority's unique expected-loss-minimizing control $c^*$ on $[0,1)$ and the corresponding high-type tipping point are
--
--   $$
--   (c^*,x_T(c^*))=
--   \begin{cases}
--   \left(1-\dfrac{\sqrt{2\lambda\bar x-p\tau^2}}{\bar x},\;
--   \dfrac{\tau\bar x}{\sqrt{2\lambda\bar x-p\tau^2}}\right),&\tau\le q,\\[5pt]
--   \left(1-\dfrac{\tau}{\bar x},\;\bar x\right),&\tau\ge q.
--   \end{cases}
--   $$
--
--   Both formulas agree when $\tau=q$. This is the basic model's closed-form decision rule (9a) and its behavioral threshold (9b).
--
--   **Formalization Note** The source formula can prescribe a negative $c$ even when Lemma 1 holds. The formal theorem adds $2\lambda\bar x-p\tau^2\le\bar x^2$ to keep its first branch in the source's admissible control set. It states strict superiority over every other admissible control, matching the proof's uniqueness claim.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), pp. 11–12 (PDF 13–14), Proposition 1, (9a)–(9b)

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- Proposition 1, (9a) and (9b), with the nonnegative-control guard. -/
theorem proposition_1 (P : Params) (hS : P.Standing)
    (hL1a : P.tau < Real.sqrt (2 * P.lam * P.xbar / P.p))
    (hL1b : 1 - 2 * P.lam * P.xbar / P.tau ^ 2 < P.p)
    (hc0 : 2 * P.lam * P.xbar - P.p * P.tau ^ 2 ≤ P.xbar ^ 2) :
    (P.tau ≤ Real.sqrt (2 * P.lam * P.xbar / (1 + P.p)) →
      let c₁ := 1 - Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) / P.xbar
      c₁ ∈ Set.Ico (0 : ℝ) 1 ∧
      (∀ c ∈ Set.Ico (0 : ℝ) 1, c ≠ c₁ → expectedLoss P c₁ < expectedLoss P c) ∧
      tippingPoint P c₁ =
        P.tau * P.xbar / Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2)) ∧
    (Real.sqrt (2 * P.lam * P.xbar / (1 + P.p)) ≤ P.tau →
      let c₂ := 1 - P.tau / P.xbar
      c₂ ∈ Set.Ico (0 : ℝ) 1 ∧
      (∀ c ∈ Set.Ico (0 : ℝ) 1, c ≠ c₂ → expectedLoss P c₂ < expectedLoss P c) ∧
      tippingPoint P c₂ = P.xbar) := by sorry

end ToneAtTop.Diversion
