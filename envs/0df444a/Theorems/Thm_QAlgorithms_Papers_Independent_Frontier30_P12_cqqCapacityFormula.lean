-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_cqqCapacityFormula
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.cqqCapacityFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:08:30.426089+00:00
-- url     : https://prove2.me/theorems/4ea354bb-7222-4be8-861c-812e15aa1dbd
-- title:
--   Theorem 6: regularized cqq secret-key capacity and range bounds
-- statement:
--   Let $\rho^{ABE}=\sum_xP(x)|x\rangle\langle x|\otimes\rho_x^{BE}$ be a finite normalized cqq state on nonempty registers. Let $K_{\to}$ denote the operational one-way key capacity with independent-copy inputs, vanishing disagreement, full $\ell_1$ nonuniformity, and every key-conditional transcript/Eve state approaching one common normalized state in full trace norm. Each protocol sequence has one finite public-rate bound $L_n\le2^{nF}$. Then
--
--   $$K_{\to}(\rho)=\lim_{n\to\infty}\frac1nK^{(1)}(\rho^{\otimes n}),\qquad K^{(1)}(\rho)=\max_{X\to U\to T}\{I(U;B|T)-I(U;E|T)\}.$$
--
--   The optimization is over arbitrary finite classical stochastic channels $Q(u|x)$ and $R(t|u)$, evaluated on the normalized state whose $(t,u,x)$ block is $R(t|u)Q(u|x)P(x)\rho_x^{BE}$. All entropies are in bits. The maximum is attained with deterministic $T=f(U)$ and $|T|\le|\mathcal X|$, $|U|\le|\mathcal X|^2$. For every regularized term these same assertions hold on the alphabet $\mathcal X^n$, with bounds $|T|\le|\mathcal X|^n$ and $|U|\le|\mathcal X|^{2n}$.
--
--   This identifies the operational capacity and also establishes existence of finite optimizers; $T$ is classical.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 5, Theorem 6

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

/-- arXiv:quant-ph/0306078v1, PDF p.5, Theorem 6; range proof pp.14--15.
The printed prose says "For very". Each n-copy optimizer has bounds for the
alphabet X^n and deterministic T=f(U). Attainment is asserted, not assumed. -/
theorem cqqCapacityFormula {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E]
    (p : X → ℝ) (W : X → Op (B × E)) (h : IsCqq p W) :
    Tendsto (fun n => cqqSingle (lawCopies p n) (cqqCopies W) / n)
      atTop (nhds (cqqKeyCapacity p W)) ∧
    (∀ n : ℕ, 0 < n → CqqRestrictedMaximum (lawCopies p n) (cqqCopies W)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
