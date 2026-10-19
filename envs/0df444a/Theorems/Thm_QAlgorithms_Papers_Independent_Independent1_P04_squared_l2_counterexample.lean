-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P04_squared_l2_counterexample
-- name    : QAlgorithms.Papers.Independent.Independent1.P04.squared_l2_counterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:35.967416+00:00
-- url     : https://prove2.me/theorems/c6d53ded-d458-481e-813f-aa1f60d28700
-- title:
--   A selective-monotonicity counterexample
-- statement:
--   Let $\alpha,\beta\in\mathbb C$ obey $|\alpha|^2+|\beta|^2=1$ and $|\beta|^2>1/3$. Define
--   $$\rho=\begin{pmatrix}1/4&0&1/4\\0&1/2&0\\1/4&0&1/4\end{pmatrix},\quad K_1=\begin{pmatrix}0&1&0\\0&0&0\\0&0&\alpha\end{pmatrix},\quad K_2=\begin{pmatrix}1&0&0\\0&0&\beta\\0&0&0\end{pmatrix}.$$
--   The matrix $\rho$ is a density matrix and these matrices form a complete incoherent instrument. For $C_2(\sigma)=\sum_{i\ne j}|\sigma_{ij}|^2$,
--   $$C_2(\rho)=\frac18<\sum_{a:p_a>0}p_aC_2(\rho_a)=\frac{|\beta|^2}{2(1+|\beta|^2)}.$$
--   The endpoint $|\beta|^2=1$ is allowed; for this particular input both branch probabilities are $1/2$. This disproves selective monotonicity.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, Appendix G (G.2)–(G.4), PDF p. 11. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq






























































/-- PDF pp.10–11, (G.2)–(G.4): selective-monotonicity failure, with null branches allowed. -/
theorem squared_l2_counterexample (alpha beta : ℂ)
    (hnorm : ‖alpha‖^2+‖beta‖^2 = 1) (hbeta : 1/3 < ‖beta‖^2) :
    IsDensityMatrix hsCounterexample ∧
    IncoherentInstrument (fun _ : Fin 2 => 3) (hsCounterKraus alpha beta) ∧
    squaredOffDiagonal hsCounterexample = 1/8 ∧
    (∑ i, selectiveContribution (fun _ => squaredOffDiagonal)
      (hsCounterKraus alpha beta i) hsCounterexample) = ‖beta‖^2/(2*(1+‖beta‖^2)) ∧
    squaredOffDiagonal hsCounterexample < ∑ i, selectiveContribution (fun _ => squaredOffDiagonal)
      (hsCounterKraus alpha beta i) hsCounterexample := by sorry




end QAlgorithms.Papers.Independent.Independent1.P04
