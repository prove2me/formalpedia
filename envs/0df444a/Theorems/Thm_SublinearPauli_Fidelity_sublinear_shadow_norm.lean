-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_sublinear_shadow_norm
-- name    : SublinearPauli.Fidelity.sublinear_shadow_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:48:21.908117+00:00
-- url     : https://prove2.me/theorems/a9010925-d167-4b29-9968-75c4e7d57122
-- title:
--   Theorem 2 — sublinear bound on the Pauli shadow norm, $\frac1{3^N}\|O\|_{\mathrm{shadow}}^2=\max_\sigma N_\sigma(O)\le\frac{A_N}{3^N}\|O\|_2^2$
-- statement:
--   Let $\lambda=\frac{1+\sqrt{33}}8$, $d=2^N$ and $A_N=2^{\lambda N}(\sqrt3)^{(1-\lambda)N}$. For every positive semidefinite $d\times d$ matrix $O$, in particular every $N$-qubit density matrix $\rho$:
--   1. the maximum of the $\sigma$-biased Pauli norm over density matrices $\sigma$ is attained and equals the normalized squared shadow norm,
--   $$\frac1{3^N}\Bigl(\|O\|^{(\mathrm{pauli})}_{\mathrm{shadow}}\Bigr)^2=\max_{\sigma\in D(\mathbb C^d)}N_\sigma(O);$$
--   2. this quantity is sublinear in $d$ times the purity:
--   $$\frac1{3^N}\Bigl(\|O\|^{(\mathrm{pauli})}_{\mathrm{shadow}}\Bigr)^2\le\frac{2^{\lambda N}(\sqrt3)^{(1-\lambda)N}}{3^N}\,\|O\|_2^2.$$
--
--   Since $A_N=d^{a}$ with $a=\lambda+(1-\lambda)\tfrac{\log_23}{2}\approx0.9674$, the squared shadow norm of every target is $o(d^{0.9675})\|O\|_2^2$, improving the linear bound $d\operatorname{Tr}[O^2]$. It is the variance bound behind Theorem 1.
--
--   **Formalization Note** The shadow norm is defined from the expression on p.6 with a supremum over density matrices; item 1 says the supremum is a maximum and equals $\max_\sigma N_\sigma(O)$. $\|O\|_2^2$ is the squared Frobenius norm.
--
--   Differences from the source:
--   - generalization: a mixed state $\rho$ → every positive semidefinite matrix $O$; reason: the extension stated on p.2 (scaling by $\operatorname{Tr}[O]$, with $O=0$ trivial), which specializes to the density matrices of Theorem 2.
--   - encoding: "$\frac1{3^N}\|\rho\|^2_{\mathrm{shadow}}=\max_\sigma N_\sigma(\rho)$" → the value is the greatest element of $\{N_\sigma(O):\sigma\text{ a density matrix}\}$; reason: states the attained maximum explicitly.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.12, Theorem 2 (informal version and PSD extension p.2; shadow norm p.6; proof §5.5 p.16)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Measurement
import Definitions.Def_SublinearPauli_Fidelity_Energies

open ClassicalShadow.Linear
open scoped ComplexOrder

namespace SublinearPauli.Fidelity

/-- **Theorem 2** (Sublinear bound on the Pauli shadow norm), p.12, with the p.2 extension to
positive semidefinite observables. With `λ = (1 + √33)/8` and `A_N = 2^{λN}(√3)^{(1−λ)N}`, for
every positive semidefinite `2^N × 2^N` matrix `O` (in particular every density matrix):
1. `(1/3^N) (‖O‖_shadow^{(pauli)})² = max_σ N_σ(O)`, the maximum over density matrices `σ` being
   attained;
2. `(1/3^N) (‖O‖_shadow^{(pauli)})² ≤ (A_N / 3^N) ‖O‖₂²`. -/
theorem sublinear_shadow_norm {N : ℕ} (O : Op N) (hO : O.PosSemidef) :
    IsGreatest {v : ℝ | ∃ σ : Op N, WildeQIT.IsDensityOperator σ ∧ v = biasedNorm σ O}
        (shadowNormSq O / (3 : ℝ) ^ N) ∧
      shadowNormSq O / (3 : ℝ) ^ N ≤ rateA N / (3 : ℝ) ^ N * frobSq O := by sorry

end SublinearPauli.Fidelity
