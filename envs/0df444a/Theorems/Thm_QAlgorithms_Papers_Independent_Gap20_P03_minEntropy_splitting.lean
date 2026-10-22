-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_minEntropy_splitting
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.minEntropy_splitting
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:19:33.573256+00:00
-- url     : https://prove2.me/theorems/4e953e30-747e-4d03-8859-b0e62f29f57d
-- title:
--   Lemma 4.2: min-entropy splitting
-- statement:
--   Let $X_0,X_1$ have any discrete joint law, with possibly different alphabets. Let $\varepsilon\ge0$ and $\alpha\in\mathbb R$ satisfy $H_\infty^\varepsilon(X_0X_1)\ge\alpha$. There is an extension of the original probability space carrying a bit $C$ such that
--   $$H_\infty^\varepsilon(X_{1-C}C)\ge\alpha/2.$$
--   The original $(X_0,X_1)$ marginal is preserved. Different alphabets are distinguished by a tag, and $C$ is part of the joint output, not a conditioning variable. This is the randomized form of min-entropy splitting.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 9, Lemma 4.2: min-entropy splitting

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Lemma 4.2, p.9 and Appendix A.3 p.19. The extension p' preserves the
original (X0,X1) law, allowing random choices on an enlarged probability space. -/
theorem minEntropy_splitting {A0 A1 : Type*} (p : PMF (A0 × A1))
    (alpha epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hentropy : (alpha:EReal) ≤ smoothJoint (fun w => p w) id epsilon) :
    ∃ pe : PMF ((A0 × A1) × Bool),
      (∀ x, massAt (fun w => pe w) Prod.fst x = p x) ∧
      ((alpha/2:ℝ):EReal) ≤ smoothJoint (fun w => pe w)
        (fun w => (selected w.1.1 w.1.2 w.2,w.2)) epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
