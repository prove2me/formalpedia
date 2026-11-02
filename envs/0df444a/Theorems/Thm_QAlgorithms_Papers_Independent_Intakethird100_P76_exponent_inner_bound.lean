-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_exponent_inner_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.exponent_inner_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:12:25.244843+00:00
-- url     : https://prove2.me/theorems/6c0d0411-fff9-4649-98bd-fcb1b036c487
-- title:
--   Theorem 4 (Inner Bound to the Capacity-Reliability-Secrecy Region)
-- statement:
--   Let $S,X,Y,Z$ be finite nonempty alphabets and let $W(x,y,z\mid s)$ be a normalized discrete memoryless broadcast channel. All entropies and information quantities are in bits. For an input law $p$, information quantities below use exactly the induced law $p(s)W(x,y,z\mid s)$.
--
--   Alice draws a uniform finite message $M$, uses a possibly stochastic encoder to excite $n$ channel uses, and observes $(M,X^n)$. A public forward message $\Phi=\phi(M,X^n)$ is visible to Bob and Eve. Their keys are $K_A=k_A(M,X^n)$ and $K_B=k_B(Y^n,\Phi)$. All design maps are fixed publicly before observations. Message and public alphabets follow the fixed-rate ceiling convention; the key alphabet at rate $R$ has exactly $2^{\lceil nR\rceil}$ labels. A weakly achievable rate $R$ has one sequence of such codes with disagreement tending to zero, $I(K_A;Z^n,\Phi)/n\to0$, and $\liminf H(K_A)/n\ge R$.
--
--   There is no excitation cost constraint. Rates and target exponents are nonnegative. Let $\mathcal R$ be the closure of triples $(R,E,F)$ attained by a single code sequence satisfying the entropy-rate lower bound and $\liminf[-\log_2\Pr(K_A\ne K_B)]/n\ge E$, $\liminf[-\log_2 I(K_A;Z^n,\Phi)]/n\ge F$. A zero error or leakage has decay rate $+\infty$. Strong achievability requires both $E>0$ and $F>0$.
--
--   For $0\le\rho\le1$ put
--   $$
--    e_1(\rho)=\rho R_\Phi-\log_2\sum_{s,y}p(s)W_Y(y\mid s)\left[\sum_x W_{X\mid Y,S}(x\mid y,s)^{1/(1+\rho)}\right]^{1+\rho},
--   $$
--   $$
--    e_2(\rho)=\rho(R_\Phi-R_M)-\log_2\sum_{x,y}\left[\sum_s p(s)W_{XY}(x,y\mid s)^{1/(1+\rho)}\right]^{1+\rho},
--   $$
--   $$
--    e_3(\rho)=\rho(R_\Phi-R_M)-\log_2\sum_y\left[\sum_{s,x}p(s)W_{XY}(x,y\mid s)^{1/(1+\rho)}\right]^{1+\rho}.
--   $$
--   Let $E_o=\min_{j=1,2,3}\max_{\rho\in[0,1]} e_j(\rho)$. Here $W_{XY}$ and $W_Y$ are the indicated channel marginals. Unsupported conditional rows have zero outer weight. The first and second displays incorporate the documented source corrections C18 and C19.
--
--   For $0<\alpha\le1$ put
--   $$
--    f(\alpha)=-\alpha(R_{\rm SK}+R_\Phi-R_M)-\log_2\sum_{s,x,z}p(s)W_{XZ}(x,z\mid s)\left[\frac{W_{XZ}(x,z\mid s)}{p_Z(z)}\right]^\alpha,
--    \qquad F_o=\sup_{0<\alpha\le1}f(\alpha).
--   $$
--   Here $p_Z$ is induced by $p$ and $W$, and null $z$ fibers contribute zero.
--
--   For a common input law $p$ and auxiliary rates $R_\Phi,R_M\ge0$ let
--   $$\widetilde{\mathcal R}(p,R_\Phi,R_M)=\{(R,E,F)\in[0,\infty)^3:E\le E_o(p,R_\Phi,R_M),\ F\le F_o(p,R,R_\Phi,R_M)\}.$$
--   Then
--   $$\bigcup_{p,R_\Phi,R_M}\widetilde{\mathcal R}(p,R_\Phi,R_M)\subseteq\mathcal R.$$
--
--   This is an operational inner bound with a common code sequence for both exponents and the required key entropy rate. The printed proof's fixed-bin exact-uniformity assertion is not assumed.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 6, Theorem 4 (Inner Bound to the Capacity-Reliability-Secrecy Region)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.6, Theorem 4, (25), using documented C18/C19. No cost constraint.
The operational region retains observationEntropyBits and simultaneous exponents; public
fixed-bin uniformity is not a hypothesis. -/
theorem exponent_inner_bound (W : DMBC S X Y Z) :
    (⋃ (p : S → ℝ) (_ : IsLaw p) (RP : ℝ) (_ : 0 ≤ RP)
      (RM : ℝ) (_ : 0 ≤ RM), innerRegion W p RP RM) ⊆ region W := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
