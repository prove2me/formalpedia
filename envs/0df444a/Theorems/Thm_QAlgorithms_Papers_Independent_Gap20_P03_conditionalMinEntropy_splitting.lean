-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_conditionalMinEntropy_splitting
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.conditionalMinEntropy_splitting
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:20:27.282992+00:00
-- url     : https://prove2.me/theorems/fcb1a474-4029-4e5f-9947-7afd51490cf1
-- title:
--   Corollary 4.3: conditional min-entropy splitting
-- statement:
--   Let $X_0,X_1,Z$ have any discrete joint law, with possibly different alphabets. Suppose $\varepsilon\ge0$ and $H_\infty^\varepsilon(X_0X_1\mid Z)\ge\alpha$, where $\alpha\in\mathbb R$. There is one classical binary extension $C$, preserving the original law, such that for every $\varepsilon'>0$,
--   $$H_\infty^{\varepsilon+\varepsilon'}(X_{1-C}\mid ZC)\ge\alpha/2-1-\log_2(1/\varepsilon').$$
--   The extension may depend on the full original joint law, including $Z$, but is chosen before $\varepsilon'$. This provides the conditional splitting tool for the storage-security arguments.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 9, Corollary 4.3: conditional min-entropy splitting

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Corollary 4.3, p.9. One and the same binary extension works for EVERY
positive epsilonPrime; the extension can depend on the full original law, including Z. -/
theorem conditionalMinEntropy_splitting {A0 A1 Z : Type*}
    (p : PMF ((A0 × A1) × Z)) (alpha epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hentropy : (alpha:EReal) ≤ smoothMin (fun w => p w) Prod.fst Prod.snd epsilon) :
    ∃ pe : PMF (((A0 × A1) × Z) × Bool),
      (∀ x, massAt (fun w => pe w) Prod.fst x = p x) ∧
      ∀ epsilonPrime : ℝ, 0 < epsilonPrime →
        ((alpha/2-1-Real.logb 2 (1/epsilonPrime):ℝ):EReal) ≤
        smoothMin (fun w => pe w) (fun w => selected w.1.1.1 w.1.1.2 w.2)
          (fun w => (w.1.2,w.2)) (epsilon+epsilonPrime) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
