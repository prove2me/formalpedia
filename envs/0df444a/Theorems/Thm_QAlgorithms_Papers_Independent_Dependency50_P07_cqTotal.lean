-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_cqTotal
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.cqTotal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:26:51.308342+00:00
-- url     : https://prove2.me/theorems/95f7a331-4286-4f27-9542-ce1115d08005
-- title:
--   Total cq common randomness and saturation
-- statement:
--   For a finite classical–quantum source $XQ$, let $C(R)$ be the operational one-way common-randomness capacity, let $D(R)=C(R)-R$, and let $D(\infty)=\sup_{R\ge0}D(R)$. The operational criterion is vanishing disagreement and Shannon key entropy on iid copies, with free private randomness and an exponentially bounded key alphabet. Then
--
--   $$D(\infty)=D(H(X|Q))=H(X)-H(X|Q)=I(X;Q).$$
--
--   Furthermore $D(R)=I(X;Q)$ for every $R\ge H(X|Q)$ with $R\ge0$. Thus the total excess randomness is reached at the cq Slepian–Wolf communication rate.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 9, §2, Remark after Lemma 4: total cq distillable CR

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF pp.9,12, Remark: total cq excess, its saturation point, and the entire constant region. -/
theorem cqTotal (E : CQData X Q) (hE : E.Valid) :
    total (cqDensity E) = crExcess (cqDensity E) (classicalGivenQuantum E) ∧
    crExcess (cqDensity E) (classicalGivenQuantum E) = shannon E.prob - classicalGivenQuantum E ∧
    shannon E.prob - classicalGivenQuantum E = ensembleInformation E ∧
    ∀ R : ℝ, classicalGivenQuantum E ≤ R → 0 ≤ R → crExcess (cqDensity E) R = ensembleInformation E := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
