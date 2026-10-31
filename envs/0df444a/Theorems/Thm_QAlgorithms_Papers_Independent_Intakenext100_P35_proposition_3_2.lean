-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_3_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_3_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:12:42.837883+00:00
-- url     : https://prove2.me/theorems/7cd61343-dea4-47a7-96f1-b17fffc2d605
-- title:
--   Proposition 3.2
-- statement:
--   The closed unit ball of $\mathcal B$ is compact for uniform convergence on compact subsets of $\mathbb C_+$. The space is a nonseparable Banach algebra. Its closed ideal $\mathcal B_0$ has equivalent full and derivative norms. The Laplace-transform algebra $\mathcal{LM}$ embeds continuously into $\mathcal B$, is not closed there, and is not norm dense, whereas
--
--   $$\overline{\mathcal{LM}}^{\mathrm{compact\,open}}=\mathcal B.$$
--
--   These distinctions specify the topologies relevant to approximation.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 7, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 3.2, arXiv:2202.03143v1, PDF page(s) 7. -/
theorem proposition_3_2
:
    (∀ fs : ℕ → AnalyticSymbol, (∀ n, BesovClass (fs n) ∧ bSize (fs n) ≤ 1) →
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ f, BesovClass f ∧ bSize f ≤ 1 ∧
        CompactConverges hp (fun n => fs (phi n)) f) ∧
    BanachAlgebraSymbols hp BesovClass bSize ∧ NotSeparableSymbols BesovClass bSize ∧
    (∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ f, BZero f →
      bSemi f ≤ ENNReal.ofReal C * bSize f ∧
      bSize f ≤ ENNReal.ofReal D * bSemi f) ∧
    BanachSymbols hp BZero bSize ∧
    (∀ f g, BZero f → BesovClass g → BZero (f * g)) ∧
    (∀ f, BesovClass f → (NormClosure BZero bSize f ↔ BZero f)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f, LM f → BesovClass f ∧ bSize f ≤ ENNReal.ofReal C * hpSize f) ∧
    (∃ f, BesovClass f ∧ ¬ LM f ∧ NormClosure LM bSize f) ∧
    (∃ f, BesovClass f ∧ ¬ NormClosure LM bSize f) ∧
    (∀ f, BesovClass f → CompactClosure hp LM f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
