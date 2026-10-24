-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_relativeEntropy_sandwich
-- name    : QAlgorithms.Papers.Independent.Support50.P21.relativeEntropy_sandwich
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:46:02.099774+00:00
-- url     : https://prove2.me/theorems/21d63d5e-3907-4031-9d24-c09a49572d0c
-- title:
--   Lemma 10
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho,\sigma$ be density operators. Write $S(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log_2\rho-\log_2\sigma)]$ when $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and $S=+\infty$ otherwise. Then
--
--   $$D_{\min}(\rho\Vert\sigma)\le S(\rho\Vert\sigma)\le D_{\max}(\rho\Vert\sigma).$$
--
--   This compares the two new divergences with support-aware Umegaki relative entropy.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 5, Lemma 10

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- Lemma 10, PDF p.5, (27): support-aware relative entropy in bits. -/
theorem relativeEntropy_sandwich (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    dMin rho sigma ≤ unnormalizedRelativeBits rho sigma ∧
    unnormalizedRelativeBits rho sigma ≤ maxRelative rho sigma := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
