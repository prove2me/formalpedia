-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P78_permutation_box_approximates_bipartite
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P78.permutation_box_approximates_bipartite
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:17:03.950985+00:00
-- url     : https://prove2.me/theorems/c96ef463-be08-4c68-b2bd-9f4c250180e2
-- title:
--   One permutation resource approximates any finite bipartite no-signaling law
-- statement:
--   Let $P(a,b\mid x,y)$ be a bipartite no-signaling conditional probability law on finite nonempty input alphabets $X,Y$ and output alphabets $A,B$. For every $\varepsilon>0$, there exist a rational normalized no-signaling law $Q$, a common denominator $d\ge2$ for its probabilities, permutations $f^{xy}$ of $[d]$, and local relabelings $r_A^x:[d]\to A$ and $r_B^y:[d]\to B$, such that
--
--   $$
--   Q(a,b\mid x,y)=\frac1d\bigl|\{u\in[d]:r_A^x(u)=a,\ r_B^y(f^{xy}(u))=b\}\bigr|,
--   \qquad \delta(Q,P)<\varepsilon.
--   $$
--
--   Here $\delta$ is worst-input total variation, and a common denominator means that every entry of $Q$ is a nonnegative integer divided by $d$. The relabelings access only the corresponding local input and local resource output.
--
--   The formula gives a single-resource simulation followed by local relabelings. The proof paragraph's printed class label $\mathcal R$ is corrected to $\mathcal D$, in agreement with the lemma and its construction; independent moderation is pending.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, PDF p. 8, Lemma 5: a permutation box approximates any bipartite no-signaling system

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma 5 and its one-resource construction: for any positive
accuracy choose a rational normalized no-signaling approximant, then a
single permutation box and local relabelings that reproduce it exactly.
The common denominator is padded to at least two. The proof paragraph's
printed R is the class-label typo corrected to D here. Independent
source-correction moderation is pending. -/
theorem permutation_box_approximates_bipartite
    {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    (P : BipartiteSystem X Y A B) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (Q : BipartiteSystem X Y A B) (d : ℕ)
      (F : X → Y → Equiv.Perm (Fin d))
      (alice : X → Fin d → A) (bob : Y → Fin d → B),
      1 < d ∧ IsRational Q.prob ∧ HasCommonProbabilityDenominator Q.prob d ∧
        relabeledKernel F alice bob = Q.prob ∧
        simulationDistance Q.prob P.prob < epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P78

end
