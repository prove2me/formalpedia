-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_two_copy_twirling
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.two_copy_twirling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:58:13.982243+00:00
-- url     : https://prove2.me/theorems/49e7983d-cbc8-4b26-8bad-4dc1daff2884
-- title:
--   Two-copy Haar twirl and embedded-swap average, (B3)–(B4) / (24)
-- statement:
--   Let $\mathcal T_d(X)=\mathbb E_U[(U\otimes U)^\dagger X(U\otimes U)]$ for normalized Haar measure on $U(d)$, and let $F_d$ swap the two copies. For $d\ge2$, put $\Pi_\pm=(I\pm F_d)/2$. Every complex operator $X$ satisfies
--   $$\mathcal T_d(X)=\frac{\operatorname{Tr}(X\Pi_+)}{\operatorname{Tr}\Pi_+}\Pi_++\frac{\operatorname{Tr}(X\Pi_-)}{\operatorname{Tr}\Pi_-}\Pi_-.$$
--   For $1\le L\le d$ and a coisometry $P_0:\mathbb C^d\to\mathbb C^L$, extend $F_L$ by zero as $\widetilde F_L=(P_0\otimes P_0)^\dagger F_L(P_0\otimes P_0)$. Then
--   $$\mathcal T_d(\widetilde F_L)=\frac{L(d-L)}{d(d^2-1)}I+\frac{L(Ld-1)}{d(d^2-1)}F_d.$$
--   For $d=1$, $\mathcal T_1(X)=X$ and $F_1=I$. This is the two-copy twirl used in the one-shot moment calculation; it uses $U\otimes U$.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 21, Two-copy Haar twirl and embedded-swap average, (B3)–(B4) / (24)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.8,21, (24),(B3),(B4). The final coefficients are checked from
Tr(F_L)=L and Tr(F_L F_d)=L^2; the antisymmetric trace is negative. Rational formulas require d>=2. The singleton twirl
is separately the identity, with F=I, rather than division by zero. -/
theorem two_copy_twirling :
    (∀ d : ℕ, 2 ≤ d → ∀ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      twoCopyTwirl d X =
        ((X * symmetryProjector d true).trace / (symmetryProjector d true).trace) •
          symmetryProjector d true +
        ((X * symmetryProjector d false).trace / (symmetryProjector d false).trace) •
          symmetryProjector d false) ∧
    (∀ d L : ℕ, 2 ≤ d → 0 < L → L ≤ d →
      ∀ P0 : Matrix (Fin L) (Fin d) ℂ, P0 * P0ᴴ = 1 →
        twoCopyTwirl d (embeddedSwap P0) =
          (((L : ℝ) / d * ((d : ℝ) - L) / ((d : ℝ)^2 - 1) : ℝ) : ℂ) • 1 +
          (((L : ℝ) / d * ((L : ℝ) * d - 1) / ((d : ℝ)^2 - 1) : ℝ) : ℂ) •
            swap (Fin d)) ∧
    (∀ X : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ, twoCopyTwirl 1 X = X) ∧
    swap (Fin 1) = (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
