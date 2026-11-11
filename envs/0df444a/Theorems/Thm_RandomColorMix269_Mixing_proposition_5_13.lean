-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_proposition_5_13
-- name    : RandomColorMix269.Mixing.proposition_5_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:52.169424+00:00
-- url     : https://prove2.me/theorems/68e3ac46-4a06-4f50-a935-1eba3bdf19c4
-- title:
--   Proposition 5.13 — spectral independence passes to marginals $\nu=\mu_U$
-- statement:
--   Let $\mu$ be a probability distribution on $[q]^V$ and $\nu=\mu_U$ its marginal on $U\subseteq V$. If $\mu$ is $\gamma$-spectrally independent (that is, $\lambda_{\max}(\Psi^\tau_\mu)\le\gamma$ under every feasible pinning $\tau$), then $\nu$ is also $\gamma$-spectrally independent:
--   $$
--   \lambda_{\max}(\Psi^\tau_\nu)\le\gamma\qquad\text{for every feasible pinning }\tau\text{ of }\nu .
--   $$
--   This transfers Corollary 1.5 from $\mu_{G,q}$ to the buffered marginal.
--
--   Differences from the source:
--   - encoding: λ_max(Ψ^τ_µ) ≤ γ → z^T M z ≤ γ‖z‖² for M = D^{1/2} Ψ^τ_µ D^{-1/2}, D = diag of the one-site probabilities; reason: M is symmetric and similar to Ψ^τ_µ, so it has the same real spectrum; the empty matrix (all sites pinned) imposes nothing
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.33, Proposition 5.13

import Definitions.Def_RandomColorMix269_Mixing_Independence

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Proposition 5.13, p.33. SI already quantifies over all feasible pinnings. -/
theorem proposition_5_13 {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (μ : (V → Fin q) → ℝ) (hμ : MarkovMixing.IsDist μ) (U : Finset V) (γ : ℝ)
    (hSI : SpectralIndependent μ γ) : SpectralIndependent (marginal μ U) γ := by sorry

end RandomColorMix269.Mixing
