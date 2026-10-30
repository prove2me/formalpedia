-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_continuousMonotoneUnique
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.continuousMonotoneUnique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:11:07.925788+00:00
-- url     : https://prove2.me/theorems/0604a71e-0728-4fe5-bb7a-6f895b530660
-- title:
--   Uniqueness of sufficiently continuous additive LOCC monotones
-- statement:
--   Let $M=(M_{a,b})$ be one real-valued functional family on all finite-dimensional bipartite density states, with positive local dimensions $a,b$. Assume tensor additivity across the grouped local cut $(A,C):(B,D)$ and non-increase under deterministic finite-round LOCC, including arbitrary finite local instruments, adaptive classical communication, ancillas, disposal, and changes of local dimension. Suppose there exist real constants $C,K$, independent of all local dimensions and states, such that
--
--   $$
--   |M_{a,b}(\rho)-M_{a,b}(\sigma)|\le C\log_2(\max\{a,b\})D_{\rm print}(\rho,\sigma)+K
--   $$
--
--   for every pair of density matrices on $\mathbb C^a\otimes\mathbb C^b$, where $D_{\rm print}=2\sqrt{1-F}$ uses root fidelity $F$. Let $\beta=(|00\rangle+|11\rangle)/\sqrt2$ and $k=M_{2,2}(|\beta\rangle\langle\beta|)$. For every unit vector $\psi$ on every such system,
--
--   $$
--   M_{a,b}(|\psi\rangle\langle\psi|)=kS(\operatorname{Tr}_B|\psi\rangle\langle\psi|),
--   $$
--
--   where $S$ is von Neumann entropy in bits. Thus the stated continuity property determines pure-state values up to this family's Bell-pair normalization, with no assumption $k=1$.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 4, Uniqueness of sufficiently continuous additive LOCC measures, (24) and conclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.

open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.

set_option maxHeartbeats 800000

/-- PDF pp.3–4, (24) and conclusion: additive deterministic-LOCC monotones
with one pair of dimension-independent continuity constants are proportional
to entropy on pure states. k is THIS family's value on a Bell pair. The accepted
finite-round LOCC channel model includes arbitrary rectangular local Kraus
instruments and outcome-dependent continuation. The
printed (10) scale is used only as the uniform hypothesis, where it is valid. -/
theorem continuousMonotoneUnique (M : EntanglementFamily)
    (hadditive : IsAdditive M)
    (hmonotone : ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
      ∀ (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
        (sigma : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ),
      IsDensityMatrix rho → IsDensityMatrix sigma →
      ∀ L : Superop (Fin a × Fin b) (Fin c × Fin d),
      FiniteLOCC L → L rho = sigma → M c d sigma ≤ M a b rho)
    (hcontinuity : ∃ C K : ℝ, ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ rho sigma : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      IsDensityMatrix rho → IsDensityMatrix sigma →
      |M a b rho - M a b sigma| ≤
        C * Real.logb 2 (max a b) * printedBures rho sigma + K) :
    ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ psi : EuclideanSpace ℂ (Fin a × Fin b), ‖psi‖ = 1 →
      M a b (pureDensity psi) =
        M 2 2 (pureDensity (bellVector 2)) * vnEntropy (traceRight (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
