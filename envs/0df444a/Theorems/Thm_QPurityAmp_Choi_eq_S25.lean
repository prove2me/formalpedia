-- Prove2me | Theorems.Thm_QPurityAmp_Choi_eq_S25
-- name    : QPurityAmp.Choi.eq_S25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:32.663205+00:00
-- url     : https://prove2.me/theorems/92200b91-b76d-4f66-9b73-9041d3ff2617
-- title:
--   Eq. (S25), p. 20 — P(C) = A·P(C′) for the Haar cost matrix C and C′ = −∫ (ρ^⊤)⁻¹ ⊗ ρ^{⊗n}
-- statement:
--   Let $d\ge 1$, $n\ge 0$ and $0<\lambda<1$. Let $C=\int\sigma_U^\top\otimes\rho_U^{\otimes n}\,dU$ be the cost matrix of the QPA problem and $C'=-\int(\rho_U^\top)^{-1}\otimes\rho_U^{\otimes n}\,dU$ the modified cost matrix of Eq. (S22), where $\sigma_U=U|0\rangle\langle 0|U^\dagger$, $\rho_U=\mathcal D_\lambda(\sigma_U)$ and $dU$ is the Haar probability measure on $U(d)$. Then
--   $$P(C)=A\,P(C'),\qquad A=\frac{\lambda\,(d(1-\lambda)+\lambda)}{d^2(1-\lambda)},$$
--   where $P=\mathrm{Id}-\frac{\mathbb I}{d}\otimes\mathrm{tr}_{\mathrm{out}}$.
--
--   Combined with Lemma S2.4, this shows that $C^\top$ and $C'^\top$ define SDPs with the same optimal solutions.
--
--   **Formalization Note** The paper states (S25) on one Schur-sampling sector, $P(C^{[\varsigma]})=AP(C'^{[\varsigma]})$; here it is stated on the full space $\mathrm{out}\otimes W^{\otimes n}$, which is the sum over the sectors. On the full space the $B$-term is $\frac{\mathbb I_d}{d}\otimes\int\rho_U^{\otimes n}\,dU$, which $P$ annihilates.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 20, Eq. (S25); p. 19, Eqs. (S22)–(S23)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix

/-- Eq. (S25), p. 20, on the full space: P(C) = A·P(C′) for the cost matrix C of p. 2 and the
modified cost matrix C′ = −∫ (ρ^⊤)⁻¹ ⊗ ρ^{⊗n} of Eq. (S22), with
A = λ(d(1−λ)+λ)/(d²(1−λ)). -/
theorem eq_S25 {d : ℕ} [NeZero d] (n : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    projP (cost d n lam) =
      ((lam * (d * (1 - lam) + lam) / ((d : ℝ) ^ 2 * (1 - lam)) : ℝ) : ℂ) •
        projP (costPrime d n lam) := by sorry

end QPurityAmp.Choi
