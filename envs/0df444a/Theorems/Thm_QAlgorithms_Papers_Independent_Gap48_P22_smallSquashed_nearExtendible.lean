-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_smallSquashed_nearExtendible
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.smallSquashed_nearExtendible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:13:45.634988+00:00
-- url     : https://prove2.me/theorems/06a2769f-ba17-4cd3-a18b-b9a860f2028b
-- title:
--   Small squashed entanglement implies proximity to k-extendibility
-- statement:
--   Let $A,B$ be finite complex quantum systems of positive dimension, and let $\rho^{AB}$ be a density operator. Entropy is measured in bits, and $E_{\rm sq}$ is half the infimum of conditional mutual information over normalized extensions of every positive finite ancillary dimension. If $E_{\rm sq}(\rho)\le\varepsilon$ with $\varepsilon\ge0$, then for every integer $k\ge1$ there is a density operator $\sigma^{AB}$ with a joint extension to $AB_1\cdots B_k$ whose $AB_i$ marginals all equal $\sigma$, and
--
--   $$\|\rho-\sigma\|_1\le(k-1)\sqrt{2\ln2}\sqrt\varepsilon.$$
--
--   The norm is the full trace norm, and extendibility is on $B$. This exact estimate gives the stated $O(\varepsilon^{1/4})$ proximity to an $\Omega(\varepsilon^{-1/4})$-extendible state as $\varepsilon\downarrow0$. It also includes $\varepsilon=0$ and $k=1$.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 3, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Theorem 1, PDF pp.3–4: full trace norm and B-side k-extendibility.
The exact bound implies the printed fourth-root O/Omega consequence as epsilon tends to zero.
Positive k and epsilon=0 are included; no minimizing extension is assumed. -/
theorem smallSquashed_nearExtendible {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hsmall : squashedEntanglement rho ≤ epsilon)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ sigma : Matrix (A × B) (A × B) ℂ, IsDensityMatrix sigma ∧ KExtendible k sigma ∧
      traceNorm (rho-sigma) ≤ ((k : ℝ)-1) * Real.sqrt (2 * Real.log 2) * Real.sqrt epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
