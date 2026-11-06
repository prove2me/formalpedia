-- Prove2me | Theorems.Thm_SilverRateSC_lemma_5_1
-- name    : SilverRateSC.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:48:15.893723+00:00
-- url     : https://prove2.me/theorems/085d4f98-09df-47a1-a717-ce834daa0ef9
-- title:
--   Lemma 5.1 — bridge and bending at a maximizing set keep $\frac18P_w(T;H)$
-- statement:
--   Fix $\kappa\ge4$, $0<\beta\le1/4$, $a=a_\beta$, $c=c_\beta$. Consider a block $H=(h_1,\dots,h_r)$ with an incoming tail whose stepsizes sum to $w$, and a nonempty admissible maximizer $T=\{t_1<\dots<t_k\}$ of $P_w(\cdot;H)$, with $b_i=h_{t_i}$ and $s_i$ from (17); the first gap includes the incoming tail. Fix $R\ge0$, $\ell_1\ge0$, $D_1>0$ with $\ell_1/D_1\le R$, and suppose
--   $$\frac c\kappa\sum_{i=1}^k(a+s_i+8)\le\frac1{128(R+1)}.$$
--   Then the bridge construction of Lemma 3.3 can be applied at $t_1$, followed by the bending construction of Lemma 3.1 at each $t_i$, $2\le i\le k$; their local trajectories satisfy (8), and the resulting pairs satisfy
--   $$\frac{D_{k+1}}{D_1}\ge\frac18P_w(T;H),\qquad \frac{\ell_{k+1}}{D_{k+1}}\le4.$$
--
--   The checkpoint score omits quadratic contraction; this lemma shows that, after accounting for it, the components still retain one eighth of the score.
--
--   Differences from the source:
--   - encoding: an incoming tail whose stepsizes sum to w → the list wl of its nonnegative stepsizes, w = wl.sum, prepended to the first gap; reason: the first gap includes the incoming tail, whose individual stepsizes enter (9) and χ_1
--   - encoding: the bridge can be applied at t_1, followed by the bending construction at each t_i; their trajectories satisfy (8) → ∃ pairs (ℓ_i, D_i)_{i ≤ k+1} from (ℓ_1, D_1) and components Φ_i with η_i > 0; Φ_1 the bridge of Lemma 3.3 with ℓ_2 = D_1η_1/2 satisfying (8) and Y_{m+1} − ℓ_2 = D_2 for every f ≥ 0; Φ_i (i ≥ 2) with the properties of Lemma 3.1 satisfying (8) with f = 0 and Y_{m+1} − ℓ_{i+1} = D_{i+1}; reason: the conditions under which the two lemmas apply and their conclusions, spelled out
--   - encoding: block, checkpoints, gaps → h : ℕ → ℝ at positions 1, …, r; t_i = ckpt (T.sort) i; i-th gap gapList h ts i; reason: same data
--   - encoding: functions on ℝ², ∂_Y, 1-smooth → EuclideanSpace ℝ (Fin 2), coordinate 1 of gradient, KatyushaNs.IsConvexLSmooth 1 (inside IsLocalComponent); reason: Lean representation; same objects
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 5.1, p.19; setting §5.1, p.19

import Mathlib
import Definitions.Def_SilverRateSC_pOf
import Definitions.Def_SilverRateSC_aBeta
import Definitions.Def_SilverRateSC_score
import Definitions.Def_SilverRateSC_bridgePhi
import Definitions.Def_SilverRateSC_IsTransfer
import Definitions.Def_SilverRateSC_IsLocalComponent
import Definitions.Def_SilverRateSC_repairChain

namespace SilverRateSC

/-- **Lemma 5.1.** Fix `κ ≥ 4` and `0 < β ≤ 1/4`, and set `a = a_β`, `c = c_β`. Consider a block
`H = (h_1, …, h_r)` with an incoming tail whose stepsizes sum to `w`, and let
`T = {t_1 < ⋯ < t_k}` be a nonempty admissible maximizer of `P_w(T; H)`, `b_i = h_{t_i}`, `s_i`
from (17); the first gap includes the incoming tail. Fix `R ≥ 0`, `ℓ_1 ≥ 0`, `D_1 > 0` with
`ℓ_1/D_1 ≤ R`, and suppose `(c/κ) ∑_{i=1}^k (a + s_i + 8) ≤ 1/(128(R + 1))` (19). Then the bridge
construction of Lemma 3.3 can be applied at `t_1`, followed by the bending construction of
Lemma 3.1 at each `t_i`, `2 ≤ i ≤ k`. Their local trajectories satisfy (8), and the resulting pairs
satisfy `D_{k+1}/D_1 ≥ (1/8) P_w(T; H)`, `ℓ_{k+1}/D_{k+1} ≤ 4`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 5.1, p. 19 (setting §5.1, p. 19).

**Formalization Note** The incoming tail is the list `wl` of its nonnegative stepsizes, `w = wl.sum`;
the block is `h : ℕ → ℝ` at positions `1, …, r`; `t_i = ckpt ts i` with `ts = T.sort (· ≤ ·)`. The
`i`-th gap is `gapList h ts i`, preceded by `wl` for `i = 1`. "Can be applied" is spelled out:
there are pairs `(ℓ_i, D_i)_{1 ≤ i ≤ k+1}` starting at `(ℓ_1, D_1)` and components `Φ_i` with
`η_i > 0` for every `i`; `Φ_1` is the bridge of Lemma 3.3 with `ℓ_2 = D_1η_1/2`, and its trajectory
satisfies (8) with `Y_{m+1} − ℓ_2 = D_2` for every sequence `f_j ≥ 0`; each `Φ_i`, `i ≥ 2`, has the
properties of a bending component (Lemma 3.1: nonnegative, convex, `1`-smooth, `∂_YΦ_i ≤ 0`,
the two zero conditions, `ℓ_{i+1} ≥ 0`) and its trajectory with `f_j = 0` satisfies (8) with
`Y_{m+1} − ℓ_{i+1} = D_{i+1}`. -/
theorem lemma_5_1 (κ β : ℝ) (hκ : 4 ≤ κ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 4) (wl : List ℝ)
    (hwl : ∀ x ∈ wl, 0 ≤ x) (r : ℕ) (h : ℕ → ℝ) (hh : ∀ j ∈ Finset.Icc 1 r, 0 ≤ h j)
    (T : Finset ℕ) (hT : T.Nonempty) (hmax : IsMaximizing (aBeta β) (cBeta β) wl.sum r h T)
    (R ℓ₁ D₁ : ℝ) (hR : 0 ≤ R) (hℓ₁ : 0 ≤ ℓ₁) (hD₁ : 0 < D₁) (hℓD : ℓ₁ / D₁ ≤ R)
    (h19 : cBeta β / κ * ∑ t ∈ T, (aBeta β + gapSum wl.sum h T t + 8) ≤ 1 / (128 * (R + 1))) :
    ∃ (ℓ D : ℕ → ℝ) (Φ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ),
      ℓ 1 = ℓ₁ ∧ D 1 = D₁ ∧
      (∀ i ∈ Finset.Icc 1 T.card, 0 < etaGap κ
          ((if i = 1 then wl else []) ++ gapList h (T.sort (· ≤ ·)) i) (ℓ i) (D i)) ∧
      Φ 1 = bridgePhi κ (wl ++ gapList h (T.sort (· ≤ ·)) 1) (ℓ 1) (D 1) ∧
      ℓ 2 = bridgeEll κ (wl ++ gapList h (T.sort (· ≤ ·)) 1) (ℓ 1) (D 1) ∧
      (∀ f : ℕ → ℝ, (∀ j, 0 ≤ f j) →
        IsTransfer κ (Φ 1) (wl ++ gapList h (T.sort (· ≤ ·)) 1) (h (ckpt (T.sort (· ≤ ·)) 1))
            (ℓ 1) (D 1) (ℓ 2) f ∧
        outExcess κ (Φ 1) (wl ++ gapList h (T.sort (· ≤ ·)) 1) (h (ckpt (T.sort (· ≤ ·)) 1))
            (ℓ 1) (D 1) (ℓ 2) f = D 2) ∧
      (∀ i ∈ Finset.Icc 2 T.card,
        0 ≤ ℓ (i + 1) ∧ IsLocalComponent (Φ i) (ℓ i) ∧ IsFlatAbove (Φ i) (ℓ (i + 1)) ∧
        IsTransfer κ (Φ i) (gapList h (T.sort (· ≤ ·)) i) (h (ckpt (T.sort (· ≤ ·)) i))
            (ℓ i) (D i) (ℓ (i + 1)) (fun _ => 0) ∧
        outExcess κ (Φ i) (gapList h (T.sort (· ≤ ·)) i) (h (ckpt (T.sort (· ≤ ·)) i))
            (ℓ i) (D i) (ℓ (i + 1)) (fun _ => 0) = D (i + 1)) ∧
      score (aBeta β) (cBeta β) wl.sum h T / 8 ≤ D (T.card + 1) / D 1 ∧
      ℓ (T.card + 1) / D (T.card + 1) ≤ 4 := by sorry

end SilverRateSC
