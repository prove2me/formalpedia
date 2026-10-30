-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_amplitude_choi_bounds
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.amplitude_choi_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:02:37.610635+00:00
-- url     : https://prove2.me/theorems/f4e041ea-a228-4c5f-bf59-3db80a990563
-- title:
--   Exact attained amplitude-damping Choi optimizations
-- statement:
--   Let $0\le\lambda\le1$, and let $\mathcal N_\lambda$ be the qubit amplitude-damping channel with Kraus matrices $\operatorname{diag}(1,\sqrt{1-\lambda})$ and $\sqrt\lambda|0\rangle\langle1|$. Its normalized Choi state is $\pi_\lambda=(\operatorname{id}\otimes\mathcal N_\lambda)(\Phi_2)$. Write $\mathrm{SEP}$ for normalized separable two-qubit states. Set $r=(\sqrt5-1)/2$ and
--
--   $$
--   F(\lambda)=\begin{cases}\log_2\!\left[\tfrac12(1+\sqrt{1-\lambda})^2\right],&\lambda\le r,\\
--   \log_2\!\left[(1+\lambda)/(2\lambda)\right],&\lambda>r.
--   \end{cases}
--   $$
--
--   Both minima below are attained, by separate comparison states, and
--
--   $$
--   \min_{\sigma\in\mathrm{SEP}}D_{\max}(\pi_\lambda\Vert\sigma)=F(\lambda),\quad
--   \min_{\substack{\sigma\in\mathrm{SEP}\\\operatorname{Tr}_B\sigma=I/2}}D_{\max}(\pi_\lambda\Vert\sigma)=\log_2(2-\lambda),\quad
--   F(\lambda)\le E_{\max}(\mathcal N_\lambda)\le\log_2(2-\lambda).
--   $$
--
--   These are exact evaluations of the two distinct Choi optimizations of Proposition 1. The second branch of $F$ is never used at zero, and the formulas agree at $r$.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 18, §V A, (56)–(57), Appendices C–D: exact Choi optimization bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF p.18, (56)-(57), Appendices C-D pp.29-32:
exact attained values of both Choi optimizations, and the resulting channel bounds.
The two feasible sets and their optimizers remain distinct. -/
theorem amplitude_choi_bounds (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    (comparisonMinimum (choiState (amplitudeDamping lambda)) false =
        (amplitudeChoiLower lambda : EReal) ∧
      ∃ sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
        comparisonFeasible false sigma ∧
        maxRelative (choiState (amplitudeDamping lambda)) sigma =
          (amplitudeChoiLower lambda : EReal)) ∧
    (comparisonMinimum (choiState (amplitudeDamping lambda)) true =
        (amplitudeValue lambda : EReal) ∧
      ∃ sigma : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
        comparisonFeasible true sigma ∧
        maxRelative (choiState (amplitudeDamping lambda)) sigma =
          (amplitudeValue lambda : EReal)) ∧
    (amplitudeChoiLower lambda : EReal) ≤ channelEMax (amplitudeDamping lambda) ∧
      channelEMax (amplitudeDamping lambda) ≤ (amplitudeValue lambda : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
