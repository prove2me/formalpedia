-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P78_rational_target_exact_permutation_reduction
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P78.rational_target_exact_permutation_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:17:40.481207+00:00
-- url     : https://prove2.me/theorems/17babff6-7557-40e7-a817-baac9d0709e8
-- title:
--   Exact single-resource reduction for rational bipartite systems
-- statement:
--   Let $P(a,b\mid x,y)$ be a normalized nonnegative bipartite no-signaling law on finite nonempty alphabets $X,Y,A,B$, and assume every entry is rational. There exist a common denominator $d\ge2$, permutations $f^{xy}$ of $[d]$, and input-local relabelings $r_A^x:[d]\to A$ and $r_B^y:[d]\to B$ for which
--
--   $$
--   P(a,b\mid x,y)=\frac1d\bigl|\{u\in[d]:r_A^x(u)=a,\ r_B^y(f^{xy}(u))=b\}\bigr|
--   \quad\text{for all }x,y,a,b.
--   $$
--
--   Thus a single permutation resource in $\mathcal D$ simulates $P$ exactly. Padding a common denominator to at least two includes deterministic targets.
--
--   The source sentence prints $\mathcal R$; the construction supplies $\mathcal D$, which is the corrected class used here. Independent moderation of this source correction is pending.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, PDF p. 8, Unnumbered exact rational case in the proof of Lemma 5 (corrected class label)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, exact rational case of Lemma 5: one D resource and input-local
relabelings reproduce a rational target exactly. Printed R is changed to D:
the constructed D(P) has arbitrary denominator-sized outputs, not binary
outputs. A denominator of one is padded to at least two. Independent
source-correction moderation is pending. -/
theorem rational_target_exact_permutation_reduction
    {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (P : BipartiteSystem X Y A B) (hrational : IsRational P.prob) :
    ∃ (d : ℕ) (F : X → Y → Equiv.Perm (Fin d))
      (alice : X → Fin d → A) (bob : Y → Fin d → B),
      1 < d ∧ HasCommonProbabilityDenominator P.prob d ∧
        relabeledKernel F alice bob = P.prob := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P78

end
