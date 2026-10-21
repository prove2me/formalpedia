-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P27_optimal_learning_fidelity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P27.optimal_learning_fidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:22:34.624976+00:00
-- url     : https://prove2.me/theorems/b720ed41-b761-4a91-8767-fad3f3b522bd
-- title:
--   Optimal one-to-two learning equals optimal estimation
-- statement:
--   Let $d\ge2$. A one-call learning protocol first chooses a fixed normalized state $\sigma$ on two $d$-dimensional registers, trains the program $\sigma_U=(U\otimes I)\sigma(U^\dagger\otimes I)$, and only later receives the two external inputs. A fixed CPTP decoder acts on the input pair and the program. The learning-comb port order is $1,((2B,2E,2A),3)$, with dimensions $d,d^3,d^2$ and a one-dimensional port $0$. Its feasible Choi operators obey
--
--   $$L\succeq0,\qquad\operatorname{Tr}_3L=I_2\otimes\rho_1,\qquad\rho_1\succeq0,\quad\operatorname{Tr}\rho_1=1.$$
--
--   Both all feasible learning combs and all fixed-probe deterministic decoders have global Haar-average fidelity at most
--
--   $$F_{\mathrm{learn}}=\begin{cases}5/d^4=5/16,&d=2,\\6/d^4,&d>2.\end{cases}$$
--
--   There exist a feasible learning comb, a normalized probe and a CPTP decoder which describe the same resulting channel for every gate and attain this value. Thus optimal one-to-two learning has exactly the same fidelity as optimal estimation, and the result includes physical attainment.
-- source:
--   Optimal cloning of unitary transformations, arXiv:0804.0129v2, PDF p. 4, Eq. (11) and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.4, Eq.(11) and following paragraph: optimal one-to-two learning equals
optimal estimation, with both universal upper bounds and physical attainment.
The printed L^(2) is a local superscript typo; this is a one-call protocol. -/
theorem optimal_learning_fidelity (d : ℕ) (hd : 2 ≤ d) :
    (∀ L : Matrix (LearnReg d) (LearnReg d) ℂ, LearningAdmissible L →
      learningScore L ≤ estimationValue d) ∧
    (∀ sigma : Matrix (PairReg d) (PairReg d) ℂ, IsDensityMatrix sigma →
      ∀ decoder : Superop (PairReg d × PairReg d) (PairReg d), IsChannel decoder →
        familyScore (learningFamily sigma decoder) ≤ estimationValue d) ∧
    ∃ L : Matrix (LearnReg d) (LearnReg d) ℂ,
      LearningAdmissible L ∧ learningScore L = estimationValue d ∧
      ∃ sigma : Matrix (PairReg d) (PairReg d) ℂ, IsDensityMatrix sigma ∧
      ∃ decoder : Superop (PairReg d × PairReg d) (PairReg d), IsChannel decoder ∧
        (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), learningChoi L U = channelChoi (learningFamily sigma decoder U)) ∧
        familyScore (learningFamily sigma decoder) = estimationValue d := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P27

end
