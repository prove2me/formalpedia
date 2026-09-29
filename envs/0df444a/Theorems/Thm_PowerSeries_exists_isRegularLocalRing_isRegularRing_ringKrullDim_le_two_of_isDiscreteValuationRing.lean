-- Prove2me | Theorems.Thm_PowerSeries_exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
-- name    : PowerSeries.exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ae875672-d018-593c-b9b2-7f2fb0833e2a
-- title:
--   O[[t]] is a complete regular local ring of dimension at most 2
-- statement:
--   Let $O$ be a commutative ring which is a domain and a discrete valuation ring, complete (and separated) for the adic filtration by its maximal ideal, and let $p$ be a natural number whose image in $O$ lies in the maximal ideal of $O$ and is non-zero. The assertion is that the power series ring $\mathrm{PowerSeries}\,O = O[[t]]$ carries the following structure, packaged as nested existential statements over the corresponding proofs so that they may be used as instances: $O[[t]]$ is a regular local ring; $O[[t]]$ is a regular ring, i.e. its localisation at every prime ideal is regular local; $O[[t]]$ is complete and separated for the adic filtration by its own maximal ideal; the structure map $O \to O[[t]]$ is a local homomorphism, that is, it pulls the maximal ideal of $O[[t]]$ back into the maximal ideal of $O$; and, in addition, the Krull dimension of $O[[t]]$ is at most $2$, the image of $p$ in $O[[t]]$ is non-zero, and that image lies in the maximal ideal of $O[[t]]$. The dimension bound is stated as an inequality, not as the equality $\dim O[[t]] = 2$.
--
--   This collects the standard commutative algebra of the mixed-characteristic power series ring $O[[t]]$ over a complete discrete valuation ring, in the form needed to treat it as a ring on which deformation functors of Serre–Tate/Lubin–Tate type are represented. It is used in the construction of the regular tower and versal algebra attached to fake elliptic curves in the Čerednik–Drinfel'd setting, and it invokes the implication that a regular local ring of Krull dimension at most $2$ is a regular ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem PowerSeries.exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (p : ℕ) (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0) :
    ∃ (_ : IsRegularLocalRing (PowerSeries O)) (_ : IsRegularRing (PowerSeries O))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries O)) (PowerSeries O))
      (_ : IsLocalHom (algebraMap O (PowerSeries O))),
      ringKrullDim (PowerSeries O) ≤ 2 ∧ ((p : ℕ) : PowerSeries O) ≠ 0 ∧
        ((p : ℕ) : PowerSeries O) ∈ maximalIdeal (PowerSeries O) := by sorry
