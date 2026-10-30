-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_trace_singlet_fraction_dual
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.trace_singlet_fraction_dual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:19:22.011538+00:00
-- url     : https://prove2.me/theorems/f0a3553f-11a5-4703-bcf7-8802947aa141
-- title:
--   Section V unnumbered: finite-error singlet-fraction formula
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. An operation is CPTP; its separability constraint applies only to the specified input and output partitions. Let $K\ge1$, $\epsilon\ge0$, and let $\Phi_K$ be the normalized maximally entangled state on the two $K$-dimensional output parties. Among CPTP maps with $\sup_{\sigma\in\mathcal S}\inf_{\pi\in\mathcal S}\|\Lambda(\sigma)-\pi\|_1\le\epsilon$,
--
--   $$\max_\Lambda\operatorname{Tr}(\Phi_K\Lambda(\rho))=\min_{Z\in\operatorname{cone}(\mathcal S)}\left[\operatorname{Tr}(\rho-Z)_++\operatorname{Tr}Z\left(\frac1K+\frac\epsilon2\right)\right].$$
--
--   Both extrema are attained, and the input separable cone includes zero. This is an explicit source correction: the printed coefficient is $1/K+\epsilon$. With the source’s full trace norm, an isotropic Bell weight $f\ge1/K$ has distance $2(f-1/K)$ from separable states, forcing the corrected coefficient. Independent moderation is pending.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 15, Section V unnumbered: finite-error singlet-fraction formula

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.15, finite-error singlet fraction: SOURCE CORRECTION.
Printed coefficient 1/K+epsilon is changed to 1/K+epsilon/2 because the
paper uses the FULL trace norm: an isotropic Bell weight f≥1/K is at distance
2(f−1/K) from the separable set. The displayed proof mechanism uniquely fixes
this coefficient. Both extrema are attained; epsilon=0 and K=1 are included.
Independent moderation of this correction is required. -/
theorem trace_singlet_fraction_dual {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) (K : ℕ) (hK : 0 < K)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ∃ f : ℝ, IsGreatest (singletFractions .trace A rho K hK epsilon) f ∧
      IsLeast {v | ∃ Z : PartyOperator A, SeparableCone A Z ∧
        v = singletDualObjective A rho Z (1 / (K : ℝ) + epsilon / 2)} f := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
