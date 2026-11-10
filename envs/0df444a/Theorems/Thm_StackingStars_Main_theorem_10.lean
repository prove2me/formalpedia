-- Prove2me | Theorems.Thm_StackingStars_Main_theorem_10
-- name    : StackingStars.Main.theorem_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:38.196382+00:00
-- url     : https://prove2.me/theorems/5aa236cb-6ed2-4808-a433-9495034a95e4
-- title:
--   Theorem 10 — structural partition of a size group into same-fine-type parts in O(r) × O(w) rectangles of total area O_ε(|C|)
-- statement:
--   Let $P_1,\dots,P_n$ be stars with reference data such that every $r_{P_i}\in(r/2,r]$ and $w_{P_i}\in(w/2,w]$, so they lie in one size group with scales $r,w>0$. Let them be packed by translations $t_i$ (pairwise disjoint interiors) inside a convex container $C$. There are a universal constant $K$ and, for each $\varepsilon>0$, a constant $K_\varepsilon$ depending only on $\varepsilon$ such that the following holds for all $0<c<0.1$ and $0<\varepsilon<c/100$. There is a partition $P=\mathcal P_1\,\dot\cup\cdots\dot\cup\,\mathcal P_m$ in which each part $\mathcal P_j$ consists of stars of one fine type $\tau_j$, and:
--
--   (i) in each part, any two placed reference points $q_{P}+t_{P}$, $q_{P'}+t_{P'}$ satisfy $|u_{\tau_j}\cdot(\cdot)|\le10\varepsilon r$ and $|d_{\tau_j}\cdot(\cdot)|\le10\varepsilon w$ for their difference;
--
--   (ii) the placed stars of $\mathcal P_j$ lie in a rectangle $B_j$ whose sides are parallel to $u_{\tau_j}$ and $d_{\tau_j}$, with lengths at most $Kr$ and $Kw$, and
--   $$\sum_{j=1}^m|B_j|\ \le\ K_\varepsilon\,|C| .$$
--
--   The theorem shows that splitting one size group by fine type costs only a constant factor. It feeds Lemma 12 and Corollary 14.
--
--   Differences from the source:
--   - generalization: P in one size group G_{a,b} of an instance, scales r = r_max/2^a, w = w_max/2^b → any r, w > 0 with r_P ∈ (r/2, r] and w_P ∈ (w/2, w] for every star; reason: every size group satisfies this with its scales, so the Lean statement specializes to the printed one
--   - encoding: O(r) × O(w) and O_ε(|C|) → side lengths ≤ K r, ≤ K w with K universal; Σ|B_j| ≤ K_ε |C| with K_ε chosen after ε only; reason: asymptotic notation made explicit; O(·) universal, O_ε depends on ε only
--   - encoding: the reference points span at most 10εr along u and 10εw along d → every pairwise difference of placed reference points has |u·Δ| ≤ 10εr and |d·Δ| ≤ 10εw; reason: the span of a finite set along a direction is its largest pairwise difference
--   - encoding: a partition P = P_1 ∪ … ∪ P_t → a map part from the stars to Fin m (empty parts allowed); reason: empty parts can be dropped and change no clause
--   - encoding: the area of a convex container C → extended nonnegative Lebesgue measure for the entire area comparison, without a boundedness hypothesis; reason: finite areas give the same inequality; infinite container area remains infinity instead of becoming zero under toReal
--   - reading: fine types for stars with L_P left of the radius (WLOG, p. 11) → fine types record the side of L_P; right-side stars use the mirrored family; reason: p. 5 says the fine type records the side; the WLOG is a mirror image, not a restriction of the input
--   - encoding: the reference data chosen arbitrarily → universally quantified over every admissible choice; reason: the paper choices are arbitrary
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 13, Theorem 10

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData
import Definitions.Def_StackingStars_Main_FineType

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 13 (PDF 15), Theorem 10. Stars `P i` with reference data `D i`, all in the size group with
scales `r, w`, packed by translations `t` in a convex container `C`. For `0 < c < 0.1`
and `0 < ε < c/100` there is a partition into parts `j < m`, each of one fine type `τ j`, such
that (i) the placed reference points of a part span at most `10εr` along `u_τ` and `10εw` along
`d_τ`; (ii) the placed stars of part `j` lie in a rectangle `B_j` with sides parallel to `u_τ`
and `d_τ` of dimensions at most `K r × K w` (`K` universal), and `Σ_j |B_j| ≤ K_ε |C|` (`K_ε`
depends only on `ε`). The area comparison uses extended nonnegative measure, so an unbounded
container is allowed without converting infinite area to zero. -/
theorem theorem_10 :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∃ Kε : ℝ, 0 < Kε ∧
      ∀ c : ℝ, 0 < c → c < 0.1 → ε < c / 100 →
      ∀ (n : ℕ) (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ (D : ∀ i, RefData (region (P i))) (r w : ℝ), 0 < r → 0 < w →
      (∀ i, (D i).InGroup r w) →
      ∀ (t : Fin n → Pt) (C : Set Pt), Convex ℝ C →
      IsPacking (fun i => translate (t i) (region (P i))) →
      (∀ i, translate (t i) (region (P i)) ⊆ C) →
      ∃ (m : ℕ) (part : Fin n → Fin m) (τ : Fin m → FineType) (p : Fin m → Pt)
        (a b : Fin m → ℝ),
        (∀ i, HasFineType r w (D i) (τ (part i))) ∧
        (∀ i i', part i = part i' →
          |dot ((τ (part i)).u r w) (((D i).q + t i) - ((D i').q + t i'))| ≤ 10 * ε * r ∧
          |dot ((τ (part i)).d r w) (((D i).q + t i) - ((D i').q + t i'))| ≤ 10 * ε * w) ∧
        (∀ j, 0 ≤ a j ∧ a j ≤ K * r ∧ 0 ≤ b j ∧ b j ≤ K * w) ∧
        (∀ i, translate (t i) (region (P i)) ⊆
          rect (p (part i)) ((τ (part i)).u r w) ((τ (part i)).d r w) (a (part i)) (b (part i))) ∧
        (∑ j, MeasureTheory.volume (rect (p j) ((τ j).u r w) ((τ j).d r w) (a j) (b j))) ≤
          ENNReal.ofReal Kε * MeasureTheory.volume C := by sorry

end StackingStars.Main
