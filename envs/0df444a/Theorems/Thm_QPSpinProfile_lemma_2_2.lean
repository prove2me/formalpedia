-- Prove2me | Theorems.Thm_QPSpinProfile_lemma_2_2
-- name    : QPSpinProfile.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:03.797458+00:00
-- url     : https://prove2.me/theorems/7092e5cd-c74c-4529-b6eb-b91cb67b1768
-- title:
--   Lemma 2.2: truncated squared conditioning with a prescribed POVM
-- statement:
--   There is a universal constant $C<\infty$ with the following property. Let $\{M_u:u\in Z\}$ be a finite-outcome one-qubit POVM whose measurement map satisfies (9) with constant $\kappa_{\mathcal M}$, let $\rho$ be an $n$-qubit state, let $n\ge p\ge2$, and let the integer $m_\star$ satisfy $0\le m_\star\le n-p$. Then there is $J\subseteq[n]$ with $|J^c|\le m_\star$ such that, measuring each qubit of $J^c$ with the POVM and forming $q(z)$ and $\rho_{J|z}$ by (7), the state
--   $$
--   \eta_J=\sum_{z:\,q(z)>0}q(z)\bigotimes_{i\in J}\rho_{i|z},\qquad\rho_{i|z}=\operatorname{Tr}_{J\setminus\{i\}}(\rho_{J|z}),
--   $$
--   is a fully separable state on $J$ and
--   $$
--   \binom{|J|}{p}^{-1}\sum_{\substack{I\subseteq J\\|I|=p}}\|\rho_I-(\eta_J)_I\|_1^2\le C\kappa_{\mathcal M}^2\frac{p^3}{m_\star+1}. \tag{11}
--   $$
--
--   The lemma is a truncated, nonsymmetric de Finetti bound: a bounded number of measured qubits suffices to make the $p$-qubit marginals on the remaining qubits close to those of a separable state.
--
--   Differences from the source:
--   - encoding: outcome set $Z$ → outcome set $\mathrm{Fin}\,t$; reason: every finite set is in bijection with some $\mathrm{Fin}\,t$
--   - encoding: $\rho_{J|z}=\operatorname{Tr}_{J^c}[K_z\rho K_z]/q(z)$ → $\operatorname{Tr}_{J^c}[M_z\rho]/q(z)$; reason: equal by cyclicity of the partial trace over the measured qubits (paper, p.15)
--   - encoding: $(\eta_J)_I$, a marginal of an operator on $J$ → the marginal of $\eta_J$ on the sites of $J$ lying in $I$, re-indexed by the sites of $I$; reason: same operator
--   - encoding: fully separable state on $J$ → element of the convex hull of pure product states on $J$, and a density operator; reason: in finite dimension mixtures of products of mixed qubit states are mixtures of pure product states
--   - encoding: $0\le m_\star\le n-p$ for integers → $p\le n$ and $m_\star\le n-p$ in $\mathbb N$; reason: same range
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Lemma 2.2, p.17 (PDF p.20), display (11)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
import Definitions.Def_QPSpinProfile_prodStatesOn
import Definitions.Def_QPSpinProfile_SatisfiesDistortion
import Definitions.Def_QPSpinProfile_etaJ

namespace QPSpinProfile

/-- **Lemma 2.2 (Truncated squared conditioning with a prescribed POVM)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.17, PDF p.20).
There is a universal constant `C` such that, for every finite-outcome one-qubit POVM `{M_u}`
satisfying (9) with constant `κ_M`, every `n`-qubit state `ρ`, `n ≥ p ≥ 2` and
`0 ≤ m⋆ ≤ n − p`, there is `J ⊆ [n]` with `|Jᶜ| ≤ m⋆` such that the state
`η_J = ∑_{z : q(z) > 0} q(z) ⊗_{i ∈ J} ρ_{i|z}` built by measuring `Jᶜ` is a fully separable state
on `J` and satisfies (11):
`C(|J|,p)^{-1} ∑_{I ⊆ J, |I| = p} ‖ρ_I − (η_J)_I‖₁² ≤ C κ_M² p³ / (m⋆ + 1)`.

**Formalization Note** The outcome set is `Fin t`. `(η_J)_I` is the marginal of `η_J` (an
operator on the qubits of `J`) on the sites of `J` lying in `I`, re-indexed by the sites of `I`.
"Fully separable state on `J`" is membership in the convex hull of the pure product states on
`J` together with being a density operator. -/
theorem lemma_2_2 : ∃ C : ℝ, 0 < C ∧
    ∀ (t : ℕ) (M : Fin t → Matrix (Fin 2) (Fin 2) ℂ) (κ : ℝ),
      DeFinettiSDP.Hierarchy.IsPOVM M → SatisfiesDistortion M κ →
      ∀ (n p m : ℕ) (ρ : Matrix (Qubits n) (Qubits n) ℂ),
        WildeQIT.IsDensityOperator ρ → 2 ≤ p → p ≤ n → m ≤ n - p →
        ∃ J : Finset (Fin n), (Finset.univ \ J).card ≤ m ∧
          etaJ M J ρ ∈ convexHull ℝ (prodStatesOn J) ∧
          WildeQIT.IsDensityOperator (etaJ M J ρ) ∧
          ((J.card.choose p : ℝ))⁻¹ * ∑ I ∈ J.powersetCard p,
              WildeQIT.traceNorm (marg (fun i => i ∈ I) ρ -
                (marg (fun s : J => s.1 ∈ I) (etaJ M J ρ)).submatrix
                  (fun x s => x ⟨s.1.1, s.2⟩) (fun x s => x ⟨s.1.1, s.2⟩)) ^ 2
            ≤ C * κ ^ 2 * (p : ℝ) ^ 3 / ((m : ℝ) + 1) := by sorry

end QPSpinProfile
