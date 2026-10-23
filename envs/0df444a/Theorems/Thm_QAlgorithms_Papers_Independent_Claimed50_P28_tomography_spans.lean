-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_tomography_spans
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.tomography_spans
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:18:44.214369+00:00
-- url     : https://prove2.me/theorems/45e545e3-10e3-4781-be59-adb204b8a2ad
-- title:
--   Complex channel and unital spans and their projectors
-- statement:
--   For $d\ge2$, let $\mathcal C$ be the physical positive Choi matrices with $\operatorname{Tr}_{\rm out}R=I$ and $\mathcal U$ those also satisfying $\operatorname{Tr}_{\rm in}R=I$. Their complex linear spans, rather than these affine sets themselves, are
--
--   $$\operatorname{span}_{\mathbb C}\mathcal C=\{R:\exists c\in\mathbb C,\ \operatorname{Tr}_{\rm out}R=cI\},$$
--   $$\operatorname{span}_{\mathbb C}\mathcal U=\{R:\exists c\in\mathbb C,\ \operatorname{Tr}_{\rm out}R=cI,\ \operatorname{Tr}_{\rm in}R=cI\}.$$
--
--   In the four paired-wire sectors of (28), the orthogonal projectors onto these spans are $Q_{\mathcal C}=P_1+P_2+P_4$ and $Q_{\mathcal U}=P_1+P_4$. Membership is equivalent to being fixed by the corresponding projector. The complex span of completely positive trace-nonincreasing Choi matrices is the full operator space. These identities specify exactly which directions reconstruction must measure; span elements need not be positive. Each of the three target spans is invariant under conjugation by U⊗V, with U,V∈SU(d).
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (31)–(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, (31)–(32): channel and unital spans, including the linked scalar in both
unital partial traces. Positivity belongs to the generating sets, not to every span element. -/
theorem tomography_spans {d : ℕ} (hd : 2 ≤ d) :
    (∀ R : Op (ChoiBasis d), R ∈ tomographyTargetSpan d .operations) ∧
    (∀ R : Op (ChoiBasis d),
      (R ∈ tomographyTargetSpan d .channels ↔ ∃ c : ℂ, QAlgorithms.traceLeft R = c • (1 : Op (Fin d))) ∧
      (R ∈ tomographyTargetSpan d .channels ↔ onOperator (targetProjector d .channels) R = R)) ∧
    (∀ R : Op (ChoiBasis d),
      (R ∈ tomographyTargetSpan d .unital ↔ ∃ c : ℂ, QAlgorithms.traceLeft R = c • (1 : Op (Fin d)) ∧
        traceInput R = c • (1 : Op (Fin d))) ∧
      (R ∈ tomographyTargetSpan d .unital ↔ onOperator (targetProjector d .unital) R = R)) ∧
    (∀ (K : TomographyDomain) (g : GroupPair d) (R : Op (ChoiBasis d)),
      R ∈ tomographyTargetSpan d K → conjugateTesterSeed g R ∈ tomographyTargetSpan d K) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
