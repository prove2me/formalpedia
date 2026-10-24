-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_quasiEntropy_properties
-- name    : QAlgorithms.Papers.Independent.Support50.P19.quasiEntropy_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:27:25.732134+00:00
-- url     : https://prove2.me/theorems/bdddaa20-f27a-40a7-afb9-b7fcc6687285
-- title:
--   Four properties of sandwiched quasi-relative entropy
-- statement:
--   For positive operators $A,B$ on a nonzero finite complex space and $\alpha>1$, let $\widetilde Q_\alpha(A\Vert B)=\operatorname{Tr}(B^{(1-\alpha)/(2\alpha)}AB^{(1-\alpha)/(2\alpha)})^\alpha$, with generalized inverses on the support and value $+\infty$ on support failure. For every unitary $U$, positive $C,D$ on another nonzero finite space, and density operator $\tau$ on that space,
--   $$\begin{aligned}\widetilde Q_\alpha(UAU^\dagger\Vert UBU^\dagger)&=\widetilde Q_\alpha(A\Vert B),\\\widetilde Q_\alpha(A\otimes C\Vert B\otimes D)&=\widetilde Q_\alpha(A\Vert B)\widetilde Q_\alpha(C\Vert D),\\\widetilde Q_\alpha(A\otimes\tau\Vert B\otimes\tau)&=\widetilde Q_\alpha(A\Vert B).\end{aligned}$$
--   In addition, if $1<\alpha\le2$, every finite probability distribution $p_x$ and positive families $A_x,B_x$ satisfy
--   $$\widetilde Q_\alpha\!\left(\sum_xp_xA_x\middle\Vert\sum_xp_xB_x\right)\le\sum_xp_x\widetilde Q_\alpha(A_x\Vert B_x).$$
--   Products and sums use extended nonnegative arithmetic, including $0\cdot\infty=0$. These four properties underpin data processing.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 12, theorem5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- PDF pp.12–13, Theorem 5: all four properties. Only joint convexity needs alpha≤2;
the tensor factor tau is a normalized density operator. -/
theorem quasiEntropy_properties [Nonempty I] [Nonempty J] (a : ℝ) (ha : 1 < a)
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∀ U : Matrix.unitaryGroup I ℂ,
      sandwichedTrace a ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ)
        ((U : Matrix I I ℂ) * B * (U : Matrix I I ℂ)ᴴ) = sandwichedTrace a A B) ∧
    (∀ C D : Matrix J J ℂ, C.PosSemidef → D.PosSemidef →
      sandwichedTrace a (Matrix.kronecker A C) (Matrix.kronecker B D) =
        sandwichedTrace a A B * sandwichedTrace a C D) ∧
    (∀ tau : {X : Matrix J J ℂ // IsDensityMatrix X}, sandwichedTrace a (Matrix.kronecker A tau.1) (Matrix.kronecker B tau.1) =
      sandwichedTrace a A B) ∧
    (a ≤ 2 → ∀ m : ℕ, ∀ p : Fin m → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x) = 1 →
      ∀ X Y : Fin m → Matrix I I ℂ, (∀ x, (X x).PosSemidef) → (∀ x, (Y x).PosSemidef) →
        sandwichedTrace a (average p X) (average p Y) ≤
          ∑ x, ENNReal.ofReal (p x) * sandwichedTrace a (X x) (Y x)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
