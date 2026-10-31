-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_examples_4_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.examples_4_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:20:32.742513+00:00
-- url     : https://prove2.me/theorems/370ec17e-051f-4bc0-a7f3-2f0437ca0a08
-- title:
--   Examples 4.2
-- statement:
--   Resolvents satisfy $r_\lambda\in\mathcal D_s$ for $s>-1$ and $\|r_\lambda\|_{\mathcal D_s,0}\le C_s/|\lambda|$. For $s>0$ and every $n\ge0$,
--
--   $$\|V^n\|_{\mathcal D_s,0}\le16\bigl(\mathrm B(s/2,1/2)+2^{-s/2}\bigr).$$
--
--   For $\nu\ge0$, $z^\nu e^{-z}\in\mathcal D_s$ exactly when $s>\nu$, and then its seminorm is at most $2\mathrm B((s-\nu)/2,1/2)\Gamma(\nu+1)$. Thus $e^{-z}\in\mathcal B\setminus\mathcal D_0$. Both arccot and its exponential belong to every $\mathcal D_s$, $s>-1$, although neither belongs to $\mathcal B$; the exponential is bounded and has no continuous boundary extension or limit along $\varepsilon+i$. These examples distinguish boundedness from derivative integrability.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 19, Examples 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Examples 4.2, arXiv:2202.03143v1, PDF page(s) 19. -/
theorem examples_4_2
:
    (∀ s : ℝ, -1 < s → ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ hp,
      D s (resolventSymbol lam) ∧
      dSemi s (resolventSymbol lam) ≤ ENNReal.ofReal (C / ‖lam‖)) ∧
    (∀ s : ℝ, 0 < s → ∀ n : ℕ, D s (fun z => scalarCayley z ^ n) ∧
      dSemi s (fun z => scalarCayley z ^ n) ≤
        ENNReal.ofReal (16 * (betaValue (s / 2) (1 / 2) + Real.rpow 2 (-s / 2)))) ∧
    (∀ s nu : ℝ, -1 < s → 0 ≤ nu →
      (D s (fun z => z ^ (nu : ℂ) * Complex.exp (-z)) ↔ nu < s) ∧
      (nu < s → dSemi s (fun z => z ^ (nu : ℂ) * Complex.exp (-z)) ≤
        ENNReal.ofReal (2 * betaValue ((s - nu) / 2) (1 / 2) * Real.Gamma (nu + 1)))) ∧
    BesovClass (fun z => Complex.exp (-z)) ∧ (¬ D 0 (fun z => Complex.exp (-z))) ∧
    (¬ BesovClass arccot) ∧ HInfinity hp (fun z => Complex.exp (arccot z)) ∧
    (∀ s : ℝ, -1 < s → D s arccot ∧ D s (fun z => Complex.exp (arccot z))) ∧
    (¬ BesovClass (fun z => Complex.exp (arccot z))) ∧
    (¬ ∃ F : AnalyticSymbol, EqOn F (fun z => Complex.exp (arccot z)) hp ∧
      ContinuousOn F closedHp) ∧
    (¬ ∃ c : ℂ, Tendsto (fun eps : ℝ => Complex.exp (arccot (point eps 1)))
      (𝓝[>] 0) (𝓝 c)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
