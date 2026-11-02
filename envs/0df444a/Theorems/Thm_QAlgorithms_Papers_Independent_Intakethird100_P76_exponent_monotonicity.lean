-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_exponent_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.exponent_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:17:29.244247+00:00
-- url     : https://prove2.me/theorems/e740a8af-9ecd-4ea9-ae69-60dbd0d21cea
-- title:
--   §V-B, unnumbered monotonicity of optimized exponents
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
--   Let $E_r(R_\Phi,R_M)=\sup_p E_o(p,R_\Phi,R_M)$ and $F_r(R_{\rm SK},R_\Phi,R_M)=\sup_p F_o(p,R_{\rm SK},R_\Phi,R_M)$, independently optimized over normalized input laws. On nonnegative rates,
--   $$E_r\text{ is nondecreasing in }R_\Phi\text{ and nonincreasing in }R_M;$$
--   $$F_r\text{ is nonincreasing in }R_\Phi,\text{ nondecreasing in }R_M,\text{ and nonincreasing in }R_{\rm SK}.$$
--
--   The optimizing input laws need not coincide, so this does not assert joint achievability of the independently optimized pair.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 9, §V-B, unnumbered monotonicity of optimized exponents

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

/-- PDF pp.9--10: all five monotonicity clauses. Separate optimizers need
not coincide, so their pair is not asserted operationally achievable. -/
theorem exponent_monotonicity (W : DMBC S X Y Z) :
    (∀ RM : ℝ, 0 ≤ RM → MonotoneOn (fun RP => optimizedReliability W RP RM) (Ici 0)) ∧
    (∀ RP : ℝ, 0 ≤ RP → AntitoneOn (fun RM => optimizedReliability W RP RM) (Ici 0)) ∧
    (∀ RK RM : ℝ, 0 ≤ RK → 0 ≤ RM →
      AntitoneOn (fun RP => inputOptimizedSecrecyExponent W RK RP RM) (Ici 0)) ∧
    (∀ RK RP : ℝ, 0 ≤ RK → 0 ≤ RP →
      MonotoneOn (fun RM => inputOptimizedSecrecyExponent W RK RP RM) (Ici 0)) ∧
    (∀ RP RM : ℝ, 0 ≤ RP → 0 ≤ RM →
      AntitoneOn (fun RK => inputOptimizedSecrecyExponent W RK RP RM) (Ici 0)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
