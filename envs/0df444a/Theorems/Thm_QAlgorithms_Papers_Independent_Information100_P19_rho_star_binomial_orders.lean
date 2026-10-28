-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_rho_star_binomial_orders
-- name    : QAlgorithms.Papers.Independent.Information100.P19.rho_star_binomial_orders
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:06:27.462471+00:00
-- url     : https://prove2.me/theorems/ffbb514b-9631-4500-b472-8d8c6f0325a7
-- title:
--   §6.5 unnumbered: minimal binomial orders for rhoStar
-- statement:
--   For $\rho_\star$, the exact rational evaluations satisfy
--   $$f_{29}(1/9)+5f_{29}(1/36)<1<f_{30}(1/9)+5f_{30}(1/36),\quad
--   5f_{12}(1/16)<1<5f_{13}(1/16).$$
--   By monotonicity, the minimal detecting binomial orders are $30$ standard and $13$ centered, with detection at every higher order. The standard moments are $(1/4,7/432)$ and do not violate interpolation; the normalized centered moments are $(5/16,5/256)$ and their interpolation ratio is $25/16>1$. This is minimality for this state within this hierarchy only.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
--
--   The state $\rho_\star$ uses the four unit vectors $\psi_1=(|00\rangle+\sqrt2|21\rangle)/\sqrt3$, $\psi_2=(|01\rangle+\sqrt2|12\rangle)/\sqrt3$, $\psi_3=(\sqrt2|02\rangle-|10\rangle)/\sqrt3$, and $\psi_4=(|11\rangle-\sqrt2|20\rangle)/\sqrt3$, via $\rho_\star=\tfrac14\sum_{j=1}^4|\psi_j\rangle\langle\psi_j|$.
--
--   Here $f_m(x)=x\sum_{a=0}^{m-1}(2a)!(1-x)^a/[4^a(a!)^2]$ is the binomial minorant of $\sqrt x$ on $[0,1]$.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 46, §6.5 unnumbered: minimal binomial orders for rhoStar

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §6.5 unnumbered: minimal binomial orders for rhoStar; arXiv:2609.29471v1, PDF pp.46, 47. -/
theorem rho_star_binomial_orders  :
    binomial 29 (1/9)+5*binomial 29 (1/36)<1 ∧
    1<binomial 30 (1/9)+5*binomial 30 (1/36) ∧
    5*binomial 12 (1/16)<1 ∧ 1<5*binomial 13 (1/16) ∧
    (∀ m : ℕ, 1 ≤ m → m<30 → binomial m (1/9)+5*binomial m (1/36)≤1) ∧
    (∀ m : ℕ, 30 ≤ m → 1<binomial m (1/9)+5*binomial m (1/36)) ∧
    (∀ m : ℕ, 1 ≤ m → m<13 → 5*binomial m (1/16)≤1) ∧
    (∀ m : ℕ, 13 ≤ m → 1<5*binomial m (1/16)) ∧
    rMoment rhoStar 1=1/4 ∧ rMoment rhoStar 2=7/432 ∧
    rMoment rhoStar 1^3<rMoment rhoStar 2 ∧
    (let Y := ((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar
     rMoment Y 1=5/16 ∧ rMoment Y 2=5/256 ∧ rMoment Y 1^3/rMoment Y 2=25/16) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
