-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P78_reduced_resource_is_permutation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P78.reduced_resource_is_permutation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:14:46.805414+00:00
-- url     : https://prove2.me/theorems/3923727e-b564-4aa0-9e98-b9332cbe2fb0
-- title:
--   The corrected smaller resource is a permutation system
-- statement:
--   Let $X$ and $Y$ be finite nonempty input alphabets, let $d>2$, and for every $(x,y)$ let $f^{xy}$ be a permutation of $[d]=\{1,\ldots,d\}$. The target permutation system assigns mass $1/d$ to each pair $(a,f^{xy}(a))$.
--
--   For a deleted label $h$, let $r_h:[d-1]\to[d]\setminus\{h\}$ replace $h$ by $d$ and leave all other labels fixed. Define the corrected smaller map, for $u=r_{\hat a}(a)$, by
--
--   $$
--   f'^{(x,\hat a)(y,\hat b)}(a)=r_{\hat b}^{-1}\!\left(\begin{cases}f^{xy}(\hat a),&f^{xy}(u)=\hat b,\\f^{xy}(u),&f^{xy}(u)\ne\hat b.\end{cases}\right).
--   $$
--
--   The graph law of these maps, with mass $1/(d-1)$, belongs to $\mathcal D$: every smaller map is a permutation and its output size is greater than one. Its local input alphabets are $X\times[d]$ and $Y\times[d]$.
--
--   This is the alphabet-reduction step used in the bipartite simulation construction. The condition in printed equation (7) is corrected as described in the audit; independent moderation of this source correction is pending.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, PDF p. 4, Lemma 1: the reduced resource is a permutation system (corrected construction)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4–5, Lemma 1 (corrected construction): Dprime belongs to D.
Printed (7) is changed to test f(r_ahat(a)) = bhat before splicing; the
printed condition can map a surviving edge to the deleted output.
The reduction is restricted to d = m+1 > 2, because D excludes size 1.
Independent source-correction moderation is pending. -/
theorem reduced_resource_is_permutation
    {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    {m : ℕ} (hm : 1 < m)
    (F : X → Y → Equiv.Perm (Fin (m + 1))) :
    IsPermutationSystem (reducedKernel (lt_trans Nat.zero_lt_one hm) F) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P78

end
