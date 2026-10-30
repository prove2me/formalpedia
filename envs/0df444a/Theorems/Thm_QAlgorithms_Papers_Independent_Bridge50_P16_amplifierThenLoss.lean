-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_amplifierThenLoss
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.amplifierThenLoss
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:40:19.949325+00:00
-- url     : https://prove2.me/theorems/7ea49d51-194b-44b2-8cea-90e424f36a35
-- title:
--   Lemma 8, Eq.(16): amplification followed by pure loss
-- statement:
--   Let $0\le\eta\le1$, $b\ge0$, and $t=\eta-(1-\eta)b>0$. With quantum-limited gain $G=\eta/t$, thermal loss decomposes as
--
--   $$\mathcal N[\eta,b]=\mathcal N[t,0]\circ\mathcal A[G].$$
--
--   This equality holds on all trace-class operators in the full Fock space. The condition $t>0$ makes the gain finite and physical. This reversed decomposition yields the improved data-processing bounds.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 4, Lemma 8, Eq.(16): amplification followed by pure loss

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Lemma 8, PDF p.4 Eq.(16), independently [18] Theorem 30 and [19] Lemma 1.
The finite physical decomposition requires t=eta-(1-eta)b>0. -/
theorem amplifierThenLoss (eta b : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hb : 0 ≤ b)
    (ht : 0 < eta - (1 - eta) * b) :
    C.IsNormalFockChannel (C.thermal eta b) ∧
    C.IsNormalFockChannel (C.thermal (eta - (1 - eta) * b) 0) ∧
    C.IsNormalFockChannel (C.amplifier (eta / (eta - (1 - eta) * b))) ∧
    B.AmplifierRealized (Real.sqrt (eta / (eta - (1 - eta) * b))) ∧
    ∀ X, B.IsTraceClass X → C.thermal eta b X =
      C.thermal (eta - (1 - eta) * b) 0 (C.amplifier (eta / (eta - (1 - eta) * b)) X) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
