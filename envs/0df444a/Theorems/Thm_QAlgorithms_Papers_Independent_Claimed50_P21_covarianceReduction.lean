-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P21_covarianceReduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P21.covarianceReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:04:51.596532+00:00
-- url     : https://prove2.me/theorems/ea5e5a24-89c3-4f1c-b9c8-2a640d5239ef
-- title:
--   Score-preserving covariance reduction and covariant optimality
-- statement:
--   Fix $d\ge2$ and normalized Haar measure on $\mathrm{SU}(d)$. Use the admissible integrable one-use instrument model and the physical scores $F,G$ of Eqs.(19)–(20). Put $A(L,W)=L_3\otimes L_2^*\otimes W_1\otimes W_0^*$, and let its channel act by $X\mapsto A(L,W)XA(L,W)^\dagger$.
--
--   Every admissible density $R$ has a positive seed $\Xi$ of trace $d^2$ commuting with $A(V,V)$ for every $V\in\mathrm{SU}(d)$. The continuous representative $S_V=A(V,I_d)\Xi A(V,I_d)^\dagger$ is admissible, has exactly the same $F$ and $G$ as $R$, and satisfies
--
--   $$
--   S_{LVW^{-1}}=A(L,W)S_VA(L,W)^\dagger\qquad(V,L,W\in\mathrm{SU}(d)).
--   $$
--
--   Pointwise, $S$ equals the displayed twirl
--
--   $$
--   S_V=\int dL\int dW\;A(L,W)R_{L^{-1}VW}A(L,W)^\dagger.
--   $$
--
--   Furthermore, for every weight $p\in[0,1]$, some such seed produces an admissible instrument globally maximizing $pG+(1-p)F$ over all admissible instruments.
--
--   This reduction retains both covariance actions and the proof's replacement assertion; continuity is asserted only for the replacement.
-- source:
--   Information - Disturbance Tradeoff in the Estimation of a Unitary Transformation, arXiv:1006.5665v2, PDF p. 6, Theorem 3 and proof, Eqs.(22)–(24)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21

noncomputable section

open MeasureTheory

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P21

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P21.matrixMeasurable

/-- PDF p.6, Theorem 3 and its proof, Eqs.(22)–(24): every original measurable
instrument has a continuous, doubly covariant replacement with exactly the same F,G.
For every weight an actual global maximizer can be chosen in this seed form. -/
theorem covarianceReduction (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    (∀ R : SU d → Matrix (Four d) (Four d) ℂ, IsHaarCombInstrument H (by omega) R →
      ∃ X : Matrix (Four d) (Four d) ℂ,
        X.PosSemidef ∧ SeedCommutes X ∧ X.trace = (d : ℂ)^2 ∧
        IsHaarCombInstrument H (by omega) (covariantDensity X) ∧ Continuous (covariantDensity X) ∧
        channelScore H (covariantDensity X) = channelScore H R ∧
        gain H (covariantDensity X) = gain H R ∧
        (∀ V, covariantDensity X V = twirl H R V) ∧
        (∀ V L W : SU d, covariantDensity X (L * V * W⁻¹) =
          covarianceAction L W (covariantDensity X V))) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∃ X : Matrix (Four d) (Four d) ℂ,
      X.PosSemidef ∧ SeedCommutes X ∧
      IsHaarCombInstrument H (by omega) (covariantDensity X) ∧
      ∀ R : SU d → Matrix (Four d) (Four d) ℂ, IsHaarCombInstrument H (by omega) R →
        p * gain H R + (1-p) * channelScore H R ≤
          p * gain H (covariantDensity X) + (1-p) * channelScore H (covariantDensity X)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P21

end
