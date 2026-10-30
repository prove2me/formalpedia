-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_one_way_key_distillation
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.one_way_key_distillation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:00:09.555061+00:00
-- url     : https://prove2.me/theorems/015d5f7c-b299-4592-80bc-1eef395d23f3
-- title:
--   One-way key distillation (95)–(97)
-- statement:
--   Let $A$ be a finite abelian group and let $(A,B,E)$ be a normalized classical source, with measurable side information. Represent its compatible marginals by probability measures $\mu_B,\mu_E$ and conditional vectors $p^B_b(a),p^E_e(a)$ with the same $A$ marginal. For positive $M,L$, one protocol chooses an independent uniform $M$-valued Alice key, samples a codeword $X$ conditional on it, and publicly sends $X'=X+A$. Bob uses $(X',B)$ and Eve sees $(X',E)$. The actual induced channels are $W_x^B(x',b)=p^B_b(x'-x)$ and $W_x^E(x',e)=p^E_e(x'-x)$. One protocol satisfies
--   $$\epsilon_B\le3\inf_{0\le s\le1}(ML)^s|A|^{-s}e^{\phi(-s|A|B)},\qquad d_1\le9\inf_{0\le t\le1/2}\frac{|A|^te^{\phi(t|A|E)}}{L^t}.$$
--   The full $L^1$ secrecy includes the entire public mask. The conditional phi function is the integral of the conditional-vector norm, rather than a conditional-Renyi replacement. For side variable $V=B$ or $E$, $\phi_V(t)=\log\mathbb E_V[(\sum_aP(a|V)^{1/(1-t)})^{1-t}]$; zero-probability letters contribute zero.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 16, One-way key distillation (95)–(97)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.16, (95)–(97): an actual one-way mask protocol. The code's
uniform key is independent of the source; Alice samples X from its stochastic
encoder and publicly sends X+A. Bob uses (X+A,B), Eve observes (X+A,E). -/
theorem one_way_key_distillation {A B E : Type*} [AddCommGroup A] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSpace E]
    (muB : Measure B) (muE : Measure E) [IsProbabilityMeasure muB] [IsProbabilityMeasure muE]
    (pB : B → A → ℝ) (pE : E → A → ℝ)
    (hp : CompatibleMarginals muB pB muE pE)
    (M L : ℕ) (hM : 0 < M) (hL : 0 < L) :
    ∃ C : WiretapCode A (A × B) M,
      wiretapDecodingError (Measure.count.prod muB) (generalAdditiveDensity pB) C ≤
        3 * sInf ((fun s : ℝ => (M * L : ℝ≥0∞) ^ s * ENNReal.ofReal
          (Real.exp (-s * Real.log (Fintype.card A : ℝ) + conditionalPhi muB pB (-s)))) ''
            Set.Icc 0 1) ∧
      codeLeakage (Measure.count.prod muE) (generalAdditiveDensity pE) C ≤
        9 * sInf ((fun t : ℝ => ENNReal.ofReal (Real.exp
          (t * Real.log (Fintype.card A : ℝ) + conditionalPhi muE pE t)) /
            (L : ℝ≥0∞) ^ t) '' Set.Icc 0 (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
