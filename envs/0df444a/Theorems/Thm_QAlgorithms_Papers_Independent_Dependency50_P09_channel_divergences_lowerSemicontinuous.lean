-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_channel_divergences_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.channel_divergences_lowerSemicontinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:13:23.063992+00:00
-- url     : https://prove2.me/theorems/7fb12e20-9711-47e4-8ebf-b00dfa0b6e6d
-- title:
--   Lemma 37
-- statement:
--   Fix finite positive-dimensional input/output systems. On the subspace of pairs $(N,M)$ with $N$ CPTP and $M$ CP, use the finite-dimensional coefficient topology. No support or finite-divergence condition is imposed. For Petz and geometric divergences take $\alpha\in(0,1)\cup(1,2]$; for sandwiched divergences take $\alpha\in[1/2,1)\cup(1,\infty)$.
--
--   $$
--   (N,M)\longmapsto D_\alpha(N\Vert M),\quad (N,M)\longmapsto\widehat D_\alpha(N\Vert M),\quad (N,M)\longmapsto\widetilde D_\alpha(N\Vert M)\quad\text{are jointly lower semicontinuous in their stated ranges}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 28, Lemma 37

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Lemma 37, arXiv:2010.01058v3, PDF pp.28.

Source correction: Printed: (149)-(150) print the sandwiched exponent -(1-alpha)/(2 alpha). Changed: Use (1-alpha)/(2 alpha). Why: At rho=sigma=I/d the printed exponent gives -2 log2 d, contradicting normalization (144) and limit (152). -/
theorem channel_divergences_lowerSemicontinuous {I : Type} [Fintype I] [Nonempty I]
    {J : Type} [Fintype J] [Nonempty J]
    (alpha : ℝ) :
    (((0 < alpha ∧ alpha < 1) ∨ (1 < alpha ∧ alpha ≤ 2)) →
        LowerSemicontinuous (pairD (I := I) (J := J) (petzD alpha)) ∧
        LowerSemicontinuous (pairD (I := I) (J := J) (geometricD alpha))) ∧
      (((1/2 ≤ alpha ∧ alpha < 1) ∨ 1 < alpha) →
        LowerSemicontinuous (pairD (I := I) (J := J) (sandwichedD alpha))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
