-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_theorem_1_2
-- name    : QuarticGauss390.EigenBound.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:39.774488+00:00
-- url     : https://prove2.me/theorems/12c68b93-2ce9-4ac3-a9d3-a48dbc16a3f3
-- title:
--   Theorem 1.2 — $\lambda_{\max}(H)\le G(H)+5\sqrt n\,\sigma$ for homogeneous quartic Majorana Hamiltonians
-- statement:
--   Let $c_1,\dots,c_{2n}$ ($n\ge2$) be Majorana operators on a Hilbert space of dimension $2^n$, satisfying $c_i^\dagger=c_i$ and $c_ic_j+c_jc_i=2\delta_{ij}I$. Let
--   $$H=\sum_{|S|=4}w_Sc_S$$
--   be a homogeneous quartic Hamiltonian with real coefficients, $\sigma=\sqrt{2^{-n}\operatorname{Tr}[H^2]}$ its normalized Frobenius norm, and $G(H)=\max_{|g\rangle\ \text{Gaussian}}\langle g|H|g\rangle$ the best energy of a pure fermionic Gaussian state (both parities). Then
--   $$\lambda_{\max}(H)\le G(H)+5\sqrt n\,\sigma .$$
--
--   Either the best Gaussian state is nearly optimal, or $\sigma$ is large relative to $\lambda_{\max}(H)/\sqrt n$; this dichotomy drives the paper's $\Omega(1/\sqrt n)$ approximation algorithm (Theorem 1.1).
--
--   Differences from the source:
--   - generalization: rational coefficients $w_S$ (p.2) → real coefficients; reason: the proof and Definition 2.2 work over $\mathbb R$, and rational coefficients are a special case
--   - encoding: $\lambda_{\max}(H)=\max_\rho\langle H\rangle_\rho$ and $G(H)=\max_g\langle H\rangle_g$ → suprema of the real parts over density matrices and over Gaussian states; reason: both sets are nonempty and bounded, both maxima are attained, and the values are real for Hermitian $H$
--   - encoding: $\sigma=\sqrt{\tau[H^2]}$ → $\sqrt{\operatorname{Re}\tau[H^2]}$; Majoranas $c_1,\dots,c_d$ → any CAR family indexed by `Fin (2n)` on bit strings `Fin n → Fin 2`; reason: $\tau[H^2]$ is real; same objects with 0-based indices
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.3, Theorem 1.2, eq. (1.5) (restated with proof p.16); model p.2, eq. (1.1), (1.2), (1.4)

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Gaussian

open Matrix

namespace QuarticGauss390.EigenBound

/-- Theorem 1.2, p.3 (proof p.16): for every homogeneous quartic Hamiltonian `H` on `n ≥ 2`
modes, `λ_max(H) ≤ G(H) + 5 √n σ` (1.5). -/
theorem theorem_1_2 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (w : Finset (Fin (2 * n)) → ℝ) :
    lambdaMax (quartic C w) ≤
      gaussOpt C (quartic C w) + 5 * Real.sqrt n * sigma n (quartic C w) := by sorry

end QuarticGauss390.EigenBound
