-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_regularizedTradeoff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.regularizedTradeoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:21:27.473456+00:00
-- url     : https://prove2.me/theorems/510040ef-fda2-4687-9fc5-7384c3ec0c46
-- title:
--   Regularization of the one-way common-randomness trade-off
-- statement:
--   Let $\rho^{AB}$ be a density operator on finite nonzero systems. All communication is noiseless and one-way from Alice to Bob; private randomness and local operations are free, and there is no initial shared randomness. For $R\ge0$, let $C(\rho,R)$ be the operational common-randomness capacity defined using disagreement probability tending to zero and key entropy per copy, with one exponential bound on the key alphabet. Let $C^{(L)}(\rho,R)$ use one fixed finite POVM on each block of $L\ge1$ copies followed by a classical–quantum protocol, with rates divided by $L$. Write $D=C-R$ and let $D(\rho,\infty)=\sup_{R\ge0}D(\rho,R)$; define $D^{(L)}(\rho,\infty)$ analogously. Then
--
--   $$C(\rho,R)=\lim_{L\to\infty}C^{(L)}(\rho,R),\qquad D(\rho,\infty)=\lim_{L\to\infty}D^{(L)}(\rho,\infty).$$
--
--   Moreover, the block variational expression is $C^{(L)}(\rho,R)=R+L^{-1}\sup_{M,U}\{I(U;B^L):I(U;X)-I(U;B^L)\le LR\}$, where $M$ is a finite POVM on $A^L$, $X$ its outcome, and $U$ a finite stochastic auxiliary generated from $X$. These convergences identify the unrestricted operational rates with the block optimizations.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 15, Abstract and §3: regularized one-way common-randomness trade-off

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

/-- PDF pp.14--15: full operational curves are limits of fixed-block curves.
Source correction: the printed block constraint is <= R; it must be <= L R because R is
per original copy. At L=1 it is exactly (23). Independent moderation of this correction is pending. -/
theorem regularizedTradeoff (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (R : ℝ) (hR : 0 ≤ R) :
    (∀ L : ℕ, 0 < L → blockCapacity rho L R =
      R + sSup (measurementValues (bipartitePower rho L) (L * R)) / L) ∧
    Tendsto (fun L : ℕ => blockCapacity rho L R) atTop (nhds (crCapacity rho R)) ∧
    Tendsto (fun L : ℕ => blockTotal rho L) atTop (nhds (total rho)) := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
