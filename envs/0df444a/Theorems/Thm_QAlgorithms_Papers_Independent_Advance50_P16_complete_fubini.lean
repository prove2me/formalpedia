-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_complete_fubini
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.complete_fubini
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:32:22.569688+00:00
-- url     : https://prove2.me/theorems/77659d31-2712-4d5b-8368-5d32f4890395
-- title:
--   Theorem 7: complete Fubini isometry
-- statement:
--   For nonzero finite dimensions $d,n$ and any $1\le p\le\infty$, the canonical Fubini and flip identifications are complete isometries:
--
--   $$L_p(M_d;L_p(M_n))\cong L_p(M_d\otimes M_n)\cong L_p(M_{dn}).$$
--
--   In particular, for every complex matrix $W$ on $\mathbb C^d\otimes\mathbb C^n$, $\|W\|_{(p,p)}=\|W_{21}\|_{(p,p)}=\|W\|_p$. Equality also holds at every positive finite matrix amplification of both identifications. For finite $p$, the last norm is $(\operatorname{Tr}|W|^p)^{1/p}$; at infinity it is the operator norm. No positivity of $W$ is required. This is the complete Fubini theorem quoted from Pisier [40], Theorem 1.9.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 15, Theorem 7: complete Fubini isometry

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Theorem 7 / (3.12), PDF p.15, quoted from Pisier [40], Theorem 1.9.
Both scalar norm identities and equality at every matrix level are retained.
Printed Tr W^p is corrected to the earlier Schatten definition Tr |W|^p;
no positivity restriction is imposed, and infinity is the operator-norm endpoint. -/
theorem complete_fubini {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (∀ W : Mat (D × I), mixedNorm p p W = schattenNorm p W ∧
      mixedNorm p p (QAlgorithms.Papers.Independent.Dependency50.P19.flip W) =
        schattenNorm p W) ∧
    (∀ a : ℕ, 0 < a → ∀ Y : Mat (Fin a × (D × I)),
      matrixMixedSize p p Y = mixedSize ⊤ p Y ∧
      matrixMixedSize p p (amplifiedFlip Y) = mixedSize ⊤ p Y) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
