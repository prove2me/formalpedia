-- Prove2me | Theorems.Thm_RossQC_Sufficient_lemma_3_5
-- name    : RossQC.Sufficient.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:43.918048+00:00
-- url     : https://prove2.me/theorems/8c36fd89-4514-4c75-ad00-89031d0521b1
-- title:
--   Lemma 3.5 — finite-horizon Lipschitz bound
-- statement:
--   Let $0<\beta<1$, $0\le\pi\le1$, and $0<C<I<R$. For any $n\ge0$ and beliefs $P_1,P_2\in[0,1]$, finite-horizon value iteration obeys
--   $$
--   |V_\beta^n(P_1)-V_\beta^n(P_2)|\le C|P_1-P_2|\frac{1-(\beta(1-\pi))^n}{1-\beta(1-\pi)}.
--   $$
--
--   The estimate controls how a change in the initial belief changes finite-horizon cost and yields the limiting estimate of Corollary 3.6.
--
--   **Formalization Note** Stage zero is $V^0=0$ and satisfies the displayed bound. The paper's beliefs range over $[0,1]$ even though the lemma says “all $P_1,P_2$.”
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 592, Lemma 3.5

import Definitions.Def_RossQC_Sufficient_Model

namespace RossQC.Sufficient

/-- Ross, Lemma 3.5, p. 592. The finite-horizon value has the stated
Lipschitz bound for beliefs `P₁`, `P₂` in `[0,1]` and every `n`, including
the zero-stage value. -/
theorem lemma_3_5 (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R)
    (n : ℕ) (P₁ P₂ : ℝ) (hP₁ : P₁ ∈ Set.Icc (0 : ℝ) 1)
    (hP₂ : P₂ ∈ Set.Icc (0 : ℝ) 1) :
    |M.valueIter n P₁ - M.valueIter n P₂| ≤
      M.C * |P₁ - P₂| *
        (1 - (M.β * (1 - M.π)) ^ n) / (1 - M.β * (1 - M.π)) := by sorry

end RossQC.Sufficient
