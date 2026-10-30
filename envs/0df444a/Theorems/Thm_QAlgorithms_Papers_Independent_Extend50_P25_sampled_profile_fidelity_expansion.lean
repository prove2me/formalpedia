-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_sampled_profile_fidelity_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.sampled_profile_fidelity_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:33:21.761193+00:00
-- url     : https://prove2.me/theorems/682170bb-dbde-4607-929d-77d5dd7b1e9d
-- title:
--   Sampled C2 profile: full fidelity expansion
-- statement:
--   Fix an integer $d\ge1$ and a nonnegative $C^2$ function $a$ on the closed ordered probability simplex, with zero boundary values and intrinsic $L^2$ norm one. Let $q_N(\mu)=a(\mu/N)^2/\sum_\nu a(\nu/N)^2$ over partitions of $N$ into at most $d$ rows, and let $F_a(N)=d^{-2}\sum_{\alpha\vdash_d N-1}(\sum_{\mu=\alpha+\square}\sqrt{q_N(\mu)})^2$ be the source profile fidelity. The normalizing sum is positive for all sufficiently large $N$, and, with constants depending only on $d,a$,
--   $$F_a(N)=1-\frac{\int_{OS_{d-1}}\|\nabla a\|^2\,dx}{dN^2}+O(N^{-3}).$$
--   The integral uses the induced Euclidean metric and volume on the sum-one hyperplane. At d=1 the energy is zero and fidelity is one.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 45, Unnumbered sampled-profile fidelity expansion; assumptions p.42, Eq.(6.25) p.43

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Unnumbered sampled-profile expansion, PDF p.45, with the full profile
assumptions on p.42 (including footnote 3): C2 up to the boundary, nonnegative,
zero boundary values and intrinsic L2 norm one. Its proof is not assumed here.
The source's eta_N is eliminated algebraically by the actual finite normalizing sum. -/
theorem sampled_profile_fidelity_expansion (d : ℕ) (hd : 1 ≤ d)
    (a : EuclideanSpace ℝ (Fin (d-1)) → ℝ)
    (ha : ContDiffOn ℝ (2 : ℕ∞) a (profileSimplex d))
    (hnonnegative : ∀ z ∈ profileSimplex d, 0 ≤ a z)
    (hboundary : ∀ z ∈ frontier (profileSimplex d), a z = 0)
    (hnormalized : Real.sqrt (d : ℝ) * (∫ z in profileSimplex d, a z ^ 2) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0,
      0 < (∑ mu : SchurDiagram d N, sampledProfileWeight d N a mu) ∧
      |sampledProfileFidelity d N a - (1 - profileEnergy d a / ((d : ℝ)*(N : ℝ)^2))| ≤
        C/(N : ℝ)^3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
