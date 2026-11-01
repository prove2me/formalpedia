-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_classicalSideInformation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.classicalSideInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:16:30.438038+00:00
-- url     : https://prove2.me/theorems/7ba7678c-7b81-4e36-9c4f-9a15d92d3fbb
-- title:
--   Unnumbered corollary: channel simulation with classical side information
-- statement:
--   Let $X,Y,Z$ be finite nonempty alphabets, $p(x)$ a probability distribution, and $W(y\mid x),V(z\mid x)$ stochastic channels. The source law is $p(x)V(z\mid x)$ and the desired joint law is $p(x)W(y\mid x)V(z\mid x)$, so $Y\to X\to Z$; $X$ and $Z$ need not be independent. Alice initially holds $X^n$, Bob holds $Z^n$, and both retain a simulated copy of $Y^n$.
--
--   For nonnegative rates $R,C$, a fully classical simulation is achievable exactly when
--   $$R\ge I(X;Y)-I(Y;Z),\qquad R+C\ge H(Y\mid Z).$$
--   For every positive error and rate slack and every sufficiently large positive $n$, codes use at most $n(R+\delta)$ forward classical bits and $n(C+\delta)$ independent uniform shared bits. The full $\ell^1$ error includes the original $X^n,Z^n$ and both output copies. Bob's diagonal POVM represents stochastic classical decoding and preserves $Z^n$.
--
--   This is the immediate classical specialization of the channel simulation theorem. In Lean, conditional states are the computed diagonal matrices $\rho_x=\sum_zV(z\mid x)|z\rangle\langle z|$, and their Holevo terms equal the displayed classical information quantities.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 19, Unnumbered corollary: channel simulation with classical side information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.19, immediate corollary: classical side information, allowing arbitrary
correlation XZ and the Markov law Y--X--Z, with the same two exact rate inequalities. -/
theorem classicalSideInformation {X : Type} [Fintype X] [Nonempty X]
    (p : X → ℝ) (hp : IsProbability p) (Z V : Auxiliary X)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    ClassicalSimulationAchievable p Z V R C ↔
      auxCost (diagonalCQSource p Z) V ≤ R ∧
        shannon (auxProb (diagonalCQSource p Z) V) - auxIQ (diagonalCQSource p Z) V ≤ R + C := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
