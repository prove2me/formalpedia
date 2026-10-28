-- Prove2me | Theorems.Thm_QPurityAmp_Choi_theorem_II_1
-- name    : QPurityAmp.Choi.theorem_II_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:40.530984+00:00
-- url     : https://prove2.me/theorems/cf5c6907-22e5-4456-83cf-665f2074ef9e
-- title:
--   Theorem II.1, p. 4 — T* = Σ_ς (d^[ς]/d^[µi*]) Π^[µi*] ⊗ I is a channel's Choi matrix, maximizes the SDP (1) and the worst-case fidelity of purifying n depolarized qudits
-- statement:
--   Let $d\ge 1$, $n\ge 0$ and $0<\lambda<1$. A protocol receives $n$ copies of $\rho=\mathcal D_\lambda(\sigma)=(1-\lambda)\sigma+\lambda\,\mathbb I_d/d$ of an unknown pure state $\sigma=|\psi\rangle\langle\psi|$ on $\mathbb C^d$ and outputs one qudit. Let
--   $$T^*=\sum_{\varsigma}\frac{d^{[\varsigma]}}{d^{[\mu_{i^*}]}}\,P_{\mu_{i^*}}\big(\mathbb I_{\mathrm{out}}\otimes\Pi_\varsigma\big),$$
--   the sum over Young diagrams $\varsigma$ with $n$ boxes and at most $d$ rows, where $i^*$ is the smallest feasible row of $\varsigma$, $[\mu_{i^*}]=\varsigma-e_{i^*}$ (the bottom box of the last column removed), $\Pi_\varsigma$ is the weak Schur sampling projector and $P_{\mu}$ the projector onto the $[\mu]$-isotypic component of $\bar U\otimes U^{\otimes n}$. In the mixed Schur basis, $T^*=U^\dagger_{\mathrm{mSch}}\bigoplus_{[\varsigma]}\frac{d^{[\varsigma]}}{d^{[\mu_{i^*}]}}\Pi^{[\mu_{i^*}]}\otimes\mathbb I_{g^{[\varsigma]}}U_{\mathrm{mSch}}$. Then:
--
--   1. **$T^*$ solves the SDP (1).** $T^*\succeq 0$, $\mathrm{tr}_{\mathrm{out}}T^*=\mathbb I_{\mathrm{in}}$, and for every $T\succeq 0$ with $\mathrm{tr}_{\mathrm{out}}T=\mathbb I_{\mathrm{in}}$,
--   $$\mathrm{Re}\,\mathrm{tr}(C^\top T)\le\mathrm{Re}\,\mathrm{tr}(C^\top T^*),\qquad C=\int\sigma_U^\top\otimes\rho_U^{\otimes n}\,dU .$$
--   2. **$T^*$ is the Choi matrix of a quantum channel:** $\Phi_{T^*}(X)=\mathrm{tr}_{\mathrm{in}}(T^*(\mathbb I\otimes X^\top))$ has a Kraus representation.
--   3. **$\Phi_{T^*}$ is the optimal QPA protocol for the minimum fidelity** of p. 2: for every quantum channel $\Phi$ from $n$ qudits to one qudit,
--   $$\min_{\|\psi\|=1}\ \langle\psi|\Phi(\rho^{\otimes n})|\psi\rangle\ \le\ \min_{\|\psi'\|=1}\ \langle\psi'|\Phi_{T^*}(\rho'^{\otimes n})|\psi'\rangle,$$
--   with $\rho=\mathcal D_\lambda(|\psi\rangle\langle\psi|)$ and $\rho'=\mathcal D_\lambda(|\psi'\rangle\langle\psi'|)$.
--
--   This is the main result of the paper: the optimal purification protocol performs Schur sampling, then, in each sector, keeps the irrep obtained by removing the bottom box of the last column, and traces out all but one register.
--
--   **Formalization Note** Item 3 is written without infima: there is a unit vector $\psi$ such that $F_\Phi(\psi)\le F_{\Phi_{T^*}}(\psi')$ for every unit vector $\psi'$; both minima are attained on the compact unit sphere, so this is the displayed inequality. Uniqueness of the optimal Choi matrix is not claimed: the proof exhibits an optimal solution. The paper works with $d\ge 2$ qudits; the statement also holds, trivially, for $d=1$ and for $n=0$, so neither is excluded. Feasible rows, the shift $\nu_i=\mu_i+(1^d)$ that names the rational irreps $[\mu_i]$, and the isotypic projectors are those of the definitions module. The Haar measure is the probability Haar measure on $U(d)$ ("a Haar-random prior on $W$", p. 2).
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 4, Theorem II.1 and Eq. (4) (= Theorem S2.2, p. 19); p. 2, Definition I.1 and the figure of merit; p. 3, Eq. (1)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix

/-- Theorem II.1, p. 4: the Choi matrix of the optimal QPA protocol is
T* = Σ_ς (d^[ς]/d^[µ_{i*}]) P_{µ_{i*}} (I ⊗ Π_ς), i* the smallest feasible row of ς:
(1) T* is feasible and optimal for the SDP (1), maximize tr(Cᵀ T) s.t. tr_out T = I, T ⪰ 0;
(2) its channel Φ_{T*} is a quantum channel;
(3) Φ_{T*} maximizes the minimum fidelity min_ψ tr(σ Φ(D_λ(σ)^{⊗n})) over all channels Φ. -/
theorem theorem_II_1 {d n : ℕ} [NeZero d] (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    IsOptimal (cost d n lam)ᵀ (optimalChoi d n) ∧
      QAlgorithms.IsChannel (choiChannel (optimalChoi d n)) ∧
      ∀ Phi : QAlgorithms.Superop (Fin n → Fin d) (Fin d), QAlgorithms.IsChannel Phi →
        ∃ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 ∧
          ∀ psi' : EuclideanSpace ℂ (Fin d), ‖psi'‖ = 1 →
            fidelity n Phi lam psi ≤ fidelity n (choiChannel (optimalChoi d n)) lam psi' := by sorry

end QPurityAmp.Choi
