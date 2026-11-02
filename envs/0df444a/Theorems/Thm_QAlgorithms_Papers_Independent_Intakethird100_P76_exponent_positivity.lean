-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P76_exponent_positivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P76.exponent_positivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:13:05.621221+00:00
-- url     : https://prove2.me/theorems/55fd813b-1a5d-4883-bfef-94c3cb74a380
-- title:
--   Proposition 5 (Positivity of Error Exponents)
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
--   For a fixed normalized input law and nonnegative rates,
--   $$R_\Phi>H(X\mid Y,S),\quad R_\Phi-R_M>H(X\mid Y,S)-I(S;Y)\quad\Longrightarrow\quad E_o>0.$$
--   Independently,
--   $$R_{\rm SK}+R_\Phi-R_M<H(X\mid Z,S)-I(S;Z)\quad\Longrightarrow\quad F_o>0.$$
--
--   The two implications characterize sufficient strict rate conditions, retaining the secrecy clause continued on the next page.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, PDF p. 6, Proposition 5 (Positivity of Error Exponents)

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

/-- PDF pp.6--7, Proposition 5, (27)--(29), with corrected C19.
Both implications are retained, including secrecy on the following page. -/
theorem exponent_positivity (W : DMBC S X Y Z) (p : S → ℝ) (hp : IsLaw p)
    (RK RP RM : ℝ) (hK : 0 ≤ RK) (hP : 0 ≤ RP) (hM : 0 ≤ RM) :
    ((condEntropy (excitationJointMass W p) obsX (fun o => (obsY o, obsS o)) < RP ∧
      condEntropy (excitationJointMass W p) obsX (fun o => (obsY o, obsS o)) -
        observationMutualInfoBits (excitationJointMass W p) obsS obsY < RP - RM) →
      0 < reliabilityExponent W p RP RM) ∧
    ((RK + RP - RM < condEntropy (excitationJointMass W p) obsX (fun o => (obsZ o, obsS o)) -
      observationMutualInfoBits (excitationJointMass W p) obsS obsZ) → 0 < secrecyExponent W p RK RP RM) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P76
