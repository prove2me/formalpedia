-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_4
-- name    : STPRideshare.Mechanism.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:38.110315+00:00
-- url     : https://prove2.me/theorems/09110144-9a99-4e1c-bd81-b4685f2edfab
-- title:
--   Lemma 4 (Lattice Structure), p. 14 — CE driver utilities form a lattice with bottom Φ_{D_i} and top Ψ_{D_i}
-- statement:
--   Let $E$ be a valid economy and let $U$ be the set of driver utility profiles $\pi=(\pi_i)_{i\in\mathcal D}$ of CE plans of $E$. Then:
--
--   1. $U$ is a lattice under the pointwise order: for $\pi,\pi'\in U$, the join $\pi\vee\pi'$ ($\max\{\pi_i,\pi'_i\}$ for each $i$) and the meet $\pi\wedge\pi'$ ($\min\{\pi_i,\pi'_i\}$) belong to $U$;
--   2. the profile $(\Phi_{D_i})_i$ of welfare gains from replicating each driver belongs to $U$ and is its least element (the driver-pessimal CE utilities);
--   3. the profile $(\Psi_{D_i})_i$ of welfare losses from removing each driver belongs to $U$ and is its greatest element (the driver-optimal CE utilities),
--
--   where
--   $$\Phi_{D_i}=W(\mathcal D\cup\{i'\},\mathcal R)-W(\mathcal D,\mathcal R),\qquad \Psi_{D_i}=W(\mathcal D,\mathcal R)-W(\mathcal D\setminus\{i\},\mathcal R).$$
--
--   The identification of the bottom of the lattice with replica gains is what the STP prices (28) are built on.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 14, Lemma 4, (20)–(21) (proof Appendix B.4)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 4 (Lattice Structure), p. 14: the driver utility profiles of CE plans are closed under
pointwise max and min; `(Φ_{D_i})_i` is the least and `(Ψ_{D_i})_i` the greatest of them. -/
theorem lemma_4 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) :
    (∀ π ∈ ceUtilities e, ∀ π' ∈ ceUtilities e,
      π ⊔ π' ∈ ceUtilities e ∧ π ⊓ π' ∈ ceUtilities e) ∧
    IsLeast (ceUtilities e) (PhiD e) ∧ IsGreatest (ceUtilities e) (PsiD e) := by sorry

end STPRideshare.Mechanism
