-- Prove2me | Theorems.Thm_SampleRemoval_Supplement_theorem_5_7
-- name    : SampleRemoval.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:24:09.4002+00:00
-- url     : https://prove2.me/theorems/ff1ee8cc-b4c2-487e-8575-5d9b39e69a7c
-- title:
--   Theorem 5.7 — non-range optima have local witnesses
-- statement:
--   Assume $n\ge4$, $2\le m\le n-1$, and LGP. Let $S$ be the unique minimizer of cross-scatter among all $m$-sets, and suppose $S$ is not a lifted-plane range. Writing $O=[n]\setminus S$, there is a five-element set $\Omega$ such that $(\Omega\cap S,\Omega\cap O)$ is the Radon partition of the five saddle lifts, $|\Omega\cap O|\in\{2,3\}$, and whichever side has two elements is an anti-monotone pair.
--
--   Moreover, $S$ remains the unique cross-scatter minimizing $m$-set in the sub-instance $S\cup(\Omega\cap O)$, and it remains non-separable by a lifted plane there.
--
--   Differences from the source:
--   - encoding: LGP, the Radon partition, and lifted-plane ranges stated geometrically → affine independence of every four lifts, strictly positive convex weights with a common lifted barycenter, and a strict linear inequality on the stated sub-instance; reason: these are equivalent finite-dimensional formulations under LGP and preserve every source instance
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 5.7, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_crossScatter
import Definitions.Def_SampleRemoval_Supplement_IsLGP
import Definitions.Def_SampleRemoval_Supplement_IsLiftedPlaneRangeOn
import Definitions.Def_SampleRemoval_Supplement_IsRadonPartition

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- **Theorem 5.7 (Non-range optima have local witnesses).** Under LGP, every unique non-range
`F`-minimizing `m`-set has a five-point Radon witness, with two or three points outside and an
anti-monotone two-element side; uniqueness and non-range status persist in the indicated
sub-instance (Xu, Gao, Hu, STOC 2027 submission, manuscript sha256 `dcd33ace…`, Theorem 5.7,
p.12 (PDF p.14)).

**Formalization Note** The section's standing assumptions `n≥4` and `2≤m≤n−1` are explicit.
`IsRadonPartition` uses strictly positive convex weights, exact under LGP. "The two-element side
is anti-monotone" is expressed for either side by the two implications below. A lifted-plane
range in the sub-instance quantifies only over `S ∪ (Ω ∩ O)`, exactly as the persistence claim
requires. -/
theorem theorem_5_7 {n m : ℕ} (p : Fin n → ℝ × ℝ) (S : Finset (Fin n))
    (hn : 4 ≤ n) (hm : 2 ≤ m ∧ m ≤ n - 1)
    (hlgp : IsLGP p)
    (hcard : S.card = m)
    (hunique : ∀ T : Finset (Fin n), T.card = m → T ≠ S →
      crossScatter p S < crossScatter p T)
    (hnrange : ¬ IsLiftedPlaneRangeOn p Finset.univ S) :
    let O := Finset.univ \ S
    ∃ Ω : Finset (Fin n),
      Ω.card = 5 ∧
      IsRadonPartition p Ω (Ω ∩ S) (Ω ∩ O) ∧
      ((Ω ∩ O).card = 2 ∨ (Ω ∩ O).card = 3) ∧
      ((Ω ∩ S).card = 2 →
        ∀ i ∈ Ω ∩ S, ∀ j ∈ Ω ∩ S, i ≠ j →
          ((p i).1 - (p j).1) * ((p i).2 - (p j).2) < 0) ∧
      ((Ω ∩ O).card = 2 →
        ∀ i ∈ Ω ∩ O, ∀ j ∈ Ω ∩ O, i ≠ j →
          ((p i).1 - (p j).1) * ((p i).2 - (p j).2) < 0) ∧
      (∀ T : Finset (Fin n), T ⊆ S ∪ (Ω ∩ O) → T.card = m → T ≠ S →
        crossScatter p S < crossScatter p T) ∧
      ¬ IsLiftedPlaneRangeOn p (S ∪ (Ω ∩ O)) S := by sorry

end SampleRemoval.Supplement
