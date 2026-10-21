-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_squashed_asymptoticallyContinuous
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.squashed_asymptoticallyContinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:43:22.320171+00:00
-- url     : https://prove2.me/theorems/c499b18a-2bf8-4349-a8eb-402d9e3cbadf
-- title:
--   Proposition 5: asymptotic continuity of all four squashed measures
-- statement:
--   Fix $m\ge2$ and choose any of the four functionals $E_F^t$, with $t=q,c$ and $F=I_m,S_m$, without $1/2$. There exist $K>0$ and a real function $h$ tending to zero at zero, depending on this choice and $m$ but independent of dimensions, such that every pair of normalized states on the same finite nonzero local spaces obeys
--
--   $$|E_F^t(\rho)-E_F^t(\sigma)|\le K\epsilon\log_2 D+h(\epsilon),\qquad \epsilon=\|\rho-\sigma\|_1.$$
--
--   Here $D$ is the total honest-system dimension and the norm is the full trace norm. No linear bound on $h$ is assumed. This is asymptotic continuity in the source's stated sense.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 7, Proposition 5: asymptotic continuity of all four squashed measures

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 5, PDF p.7: all four measures. The modulus h depends only
on epsilon and tends to zero; no linear O(epsilon) condition is substituted. -/
theorem squashed_asymptoticallyContinuous (m : ℕ) (hm : 2 ≤ m) :
    ∀ (classical : Bool) (kind : InformationKind),
      ∃ K : ℝ, 0 < K ∧ ∃ h : ℝ → ℝ,
      Filter.Tendsto h (nhds 0) (nhds 0) ∧
      ∀ (D : Fin m → Type) [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
      (rho sigma : Matrix (RegisterBasis D) (RegisterBasis D) ℂ),
      IsDensityMatrix rho → IsDensityMatrix sigma →
      |multipartiteSquashed classical kind rho - multipartiteSquashed classical kind sigma| ≤
        K * traceNorm (rho-sigma) * Real.logb 2 (Fintype.card (RegisterBasis D)) +
          h (traceNorm (rho-sigma)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
