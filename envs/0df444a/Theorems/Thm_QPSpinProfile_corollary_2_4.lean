-- Prove2me | Theorems.Thm_QPSpinProfile_corollary_2_4
-- name    : QPSpinProfile.corollary_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:26:44.22603+00:00
-- url     : https://prove2.me/theorems/7ce26aa5-5d6d-46f8-a9f5-8d9819db82a8
-- title:
--   Corollary 2.4: canonical form of the conditioning approximation
-- statement:
--   There is a universal constant $C_0<\infty$ such that for every $n$-qubit state $\rho$, integers $n\ge p\ge2$ and $0\le m_\star\le n-p$, there exist $J\subseteq[n]$ with $|J^c|\le m_\star$ and a fully separable $n$-qubit state $\sigma$ with
--   $$
--   \|M_J(f_\rho-f_\sigma)\|_{n,p}\le r_{p,m_\star}:=C_0\frac{2^{p/2}p^{3/2}}{\sqrt{m_\star+1}}. \tag{20}
--   $$
--
--   It converts the trace-norm bound of Lemma 2.2 into the canonical norm of the Hamiltonian's Gaussian process, and shows that $\mathrm{prod}_n$ is a conditioning benchmark for every class.
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: fully separable $n$-qubit state → element of the convex hull of $\mathrm{prod}_n$; reason: mixtures of products of mixed qubit states are mixtures of pure product states in finite dimension
--   - encoding: $2^{p/2}$ → $(\sqrt2)^p$; reason: equal
--   - encoding: $0\le m_\star\le n-p$ for integers → $p\le n$ and $m_\star\le n-p$ in $\mathbb N$; reason: same range
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Corollary 2.4, p.21 (PDF p.24), display (20)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QPSpinProfile_profile
import Definitions.Def_QPSpinProfile_prodStatesOn

namespace QPSpinProfile

/-- **Corollary 2.4 (Canonical form of the conditioning approximation)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.21, PDF p.24).
There is a universal constant `C₀` such that for every `n`-qubit state `ρ`, integers
`n ≥ p ≥ 2` and `0 ≤ m⋆ ≤ n − p`, there are `J ⊆ [n]` with `|Jᶜ| ≤ m⋆` and a fully separable
`n`-qubit state `σ` with (20):
`‖M_J(f_ρ − f_σ)‖_{n,p} ≤ r_{p,m⋆} := C₀ 2^{p/2} p^{3/2} / √(m⋆ + 1)`. -/
theorem corollary_2_4 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (n p m : ℕ) (ρ : Matrix (Qubits n) (Qubits n) ℂ),
      WildeQIT.IsDensityOperator ρ → 2 ≤ p → p ≤ n → m ≤ n - p →
      ∃ J : Finset (Fin n), (Finset.univ \ J).card ≤ m ∧
        ∃ σ ∈ convexHull ℝ (prodStates n),
          profileNorm (coordProj J (profile p ρ - profile p σ))
            ≤ C₀ * Real.sqrt 2 ^ p * (p : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt ((m : ℝ) + 1) := by sorry

end QPSpinProfile
