-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_canonical_position_momentum
-- name    : QAlgorithms.Papers.Independent.Next46.P20.canonical_position_momentum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:18:59.913097+00:00
-- url     : https://prove2.me/theorems/d5abec75-6cce-4cdb-ac67-28944c623240
-- title:
--   Canonical position and momentum with maximal weak domains
-- statement:
--   Let $n\ge1$, let $\chi\in L^2(\mathbb R^n)$ have norm one, and fix $j\in\{1,\ldots,n\}$. On their maximal $L^2$ domains, configuration multiplication by $x_j$ and weak momentum $-i\partial_{x_j}$ transport to the same expressions on $\mathcal H_\chi$:
--   $$
--   T_\chi x_j T_\chi^*=x_j,\qquad
--   T_\chi(-i\partial_{x_j})T_\chi^*=-i\partial_{x_j}.
--   $$
--   Each equality identifies the entire operator graph: the phase-space domain is the transported configuration domain. Derivatives are weak derivatives in $x$ only, and wave-function equalities are almost everywhere.
--
--   No differentiability of the window in $p$ is required.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 9, Remark 2.8: canonical position and momentum representations

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.9, Remark 2.8: both multiplication and -i weak x-derivative are
transported with their maximal L2 domains. Arbitrary unit L2 windows are allowed. -/
theorem canonical_position_momentum {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1) (j : Fin n) :
    transportGraph chi (positionGraph (fun x : Configuration n => x j)) =
      (restrictGraph (positionGraph (fun z : PhaseCoordinates n => (phasePosition z) j))
        (windowSpace chi : Set (PhaseL2 n)) ∩ {q | q.2 ∈ windowSpace chi}) ∧
    transportGraph chi (momentumGraph (Pi.single j 1 : Configuration n)) =
      (restrictGraph
        (momentumGraph (phasePoint (Pi.single j 1 : Configuration n) 0))
        (windowSpace chi : Set (PhaseL2 n)) ∩ {q | q.2 ∈ windowSpace chi}) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
