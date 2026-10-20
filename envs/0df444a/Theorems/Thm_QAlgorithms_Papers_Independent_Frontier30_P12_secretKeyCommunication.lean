-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_secretKeyCommunication
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.secretKeyCommunication
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:05:26.909665+00:00
-- url     : https://prove2.me/theorems/b76e3431-b943-4135-851f-a1dbff2789cd
-- title:
--   Remark 2: communication cost of the secret-key construction
-- statement:
--   For the finite normalized cqq source $\rho^{ABE}=\sum_xP(x)|x\rangle\langle x|\otimes\rho_x^{BE}$, suppose $R=I(X;B)-I(X;E)>0$. There is one sequence of finite one-way key protocols meeting all three operational security and reliability criteria, with a single bound $L_n\le2^{nF}$, such that
--
--   $$\lim_{n\to\infty}\frac{\log_2M_n}{n}=R,\qquad \lim_{n\to\infty}\frac{\log_2L_n}{n}=H(P)-I(X;B)=H(A|B).$$
--
--   Here $M_n$ is the key alphabet size and $L_n$ is the public transcript alphabet size, received by both Bob and Eve. All entropies are in bits. The cost includes the type announcement, whose contribution per copy vanishes.
--
--   This is the attained rate and communication pair of the construction, with no communication-optimality assertion.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 4, Remark 2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.4, Remark 2. The SAME evaluated protocol
sequence attains the key yield and this communication cost; no optimality claim. -/
theorem secretKeyCommunication {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E]
    (p : X → ℝ) (W : X → Op (B × E)) (h : IsCqq p W)
    (hpos : 0 < cqqAdvantage p W) :
    ∃ P : (n : ℕ) → CqqProtocol X B n,
      CqqAchieves p W P (cqqAdvantage p W) ∧
      Tendsto (fun n => Real.logb 2 ((P n).l : ℝ) / n) atTop
        (nhds (shannon p - labelInformation p (fun x => QAlgorithms.traceRight (W x)))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
