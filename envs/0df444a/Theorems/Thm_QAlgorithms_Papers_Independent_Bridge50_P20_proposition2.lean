-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_proposition2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.proposition2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:04:20.289999+00:00
-- url     : https://prove2.me/theorems/c23d0726-71c9-4965-a275-235e67fcf6c3
-- title:
--   Exact amplitude-damping channel max-relative entanglement
-- statement:
--   For $0\le\lambda\le1$, let $\mathcal N_\lambda$ be the qubit amplitude-damping channel with Kraus matrices $\operatorname{diag}(1,\sqrt{1-\lambda})$ and $\sqrt\lambda|0\rangle\langle1|$. Then
--
--   $$
--   E_{\max}(\mathcal N_\lambda)=\log_2(2-\lambda).
--   $$
--
--   The left side is the channel quantity, optimized over all normalized mixed inputs with arbitrary finite reference registers. The identity-channel endpoint $\lambda=0$ gives one bit; the constant-output endpoint $\lambda=1$ gives zero.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 18, Proposition 2, (58): exact amplitude-damping channel E_max

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

/-- arXiv:1707.05543v2, PDF p.18, Proposition 2 (58), Appendix E pp.32-40:
exact max-relative entropy of the amplitude-damping channel, including both endpoints. -/
theorem proposition2 (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    channelEMax (amplitudeDamping lambda) = (Real.logb 2 (2 - lambda) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
