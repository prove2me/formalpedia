-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_generalSecretKeyCapacityFormula
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.generalSecretKeyCapacityFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:09:14.266029+00:00
-- url     : https://prove2.me/theorems/12983cdc-77f1-4537-94e1-17512ae44ae7
-- title:
--   Theorem 8: general-state secret-key capacity and POVM bounds
-- statement:
--   Let $\rho^{ABE}$ be any normalized density operator on finite complex registers of positive dimension; Eve need not hold a purification. Let $K_{\to}(\rho)$ be defined by evaluated one-way protocols: Alice measures $(Q_{\ell m})$, Bob uses a POVM conditional on the public transcript $\ell$, Eve receives that transcript, the three key-error criteria tend to zero, and one finite $F$ bounds $L_n\le2^{nF}$. Then, with all entropies in bits,
--
--   $$K_{\to}(\rho)=\lim_{n\to\infty}\frac1nK^{(1)}(\rho^{\otimes n}),\qquad K^{(1)}(\rho)=\max_{Q,R}\{I(X;B|T)-I(X;E|T)\}.$$
--
--   The maximization allows all finite POVMs $Q=(Q_x)$ on $A$ and stochastic classical channels $R(t|x)$. Its information quantities are evaluated on the normalized block state
--
--   $$\omega^{TXBE}=\sum_{t,x}R(t|x)|t\rangle\langle t|\otimes|x\rangle\langle x|\otimes\operatorname{Tr}_A\!\left[\rho^{ABE}(Q_x\otimes\mathbf1^{BE})\right].$$
--
--   An optimizer exists with deterministic $T=f(X)$, $|T|\le d_A^2$, and $|X|\le d_A^4$. For the $n$-copy term replace $d_A$ by $d_A^n$.
--
--   **Source correction.** The printed limit omits $1/n$, and the printed block state adds an extra $P(x)$. The preceding measurement formula and explicit p.6 converse fix these two defects. Independent moderation of these corrections is pending.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 5, Theorem 8

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

/-- arXiv:quant-ph/0306078v1, PDF pp.5--6, Theorem 8; range proof p.15.
SOURCE CORRECTIONS: printed lim K^(1)(rho^n) becomes lim K^(1)(rho^n)/n,
as fixed by the explicit p.6 converse. The printed omega multiplies an already
unnormalized measurement block by P(x); that redundant factor is omitted,
as fixed by the immediately preceding measured-state formula. -/
theorem generalSecretKeyCapacityFormula {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    [Nonempty A] [Nonempty B] [Nonempty E]
    (rho : Op (A × (B × E))) (h : QAlgorithms.IsDensityMatrix rho) :
    Tendsto (fun n => quantumKeySingle (triCopies rho n) / n)
      atTop (nhds (quantumKeyCapacity rho)) ∧
    (∀ n : ℕ, 0 < n → QuantumRestrictedMaximum (triCopies rho n)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
