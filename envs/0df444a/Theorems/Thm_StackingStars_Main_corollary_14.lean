-- Prove2me | Theorems.Thm_StackingStars_Main_corollary_14
-- name    : StackingStars.Main.corollary_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:46:37.955733+00:00
-- url     : https://prove2.me/theorems/6650fa8a-5aa8-4fb9-817f-368a331e8c6d
-- title:
--   Corollary 14 — the bowls of a size group pack as stacks into O(r) × O(w) rectangles of total area O(OPT′)
-- statement:
--   Let $P_1,\dots,P_n$ be stars in the size group with scales $r,w>0$, star $i$ of fine type $\tau_i$, and let $Q(P_i)=Q_{\tau_i}(P_i)$ be the bowls of Lemma 11. There is a universal constant $K$ such that the bowls can be translated into rectangles $B_1,\dots,B_m$ with the following properties:
--
--   * every bowl in $B_j$ comes from a star of one common fine type $\tau'_j$, and $B_j$ has sides parallel to $u_{\tau'_j},d_{\tau'_j}$ of lengths at most $Kr$ and $Kw$;
--   * the bowls in one rectangle have pairwise disjoint interiors and pairwise disjoint separators, so they form a stack;
--   * $$\sum_{j}|B_j|\ \le\ K\cdot\mathrm{OPT}'(P).$$
--
--   As in $\mathrm{OPT}'$, the rectangles are separate containers. Bowls in different rectangles do not interact.
--
--   Differences from the source:
--   - generalization: P in a size group G_{a,b} of an instance → stars with r_P ∈ (r/2, r], w_P ∈ (w/2, w] for any r, w > 0; reason: every size group satisfies this
--   - encoding: Q = {Q(P)} → the bowls (D i).bowl r w (τ i) of Lemma 11, each star fine type supplied with HasFineType; reason: the fine type of a star is unique, so this is the paper Q
--   - encoding: a packing of Q into rectangles → translations, a map from bowls to rectangles, interior-disjointness and disjoint separators within each rectangle; reason: the rectangles are separate containers as in OPT′; the stack condition is the paper definition
--   - encoding: O(r) × O(w) and O(OPT′(P)) → one universal K; reason: asymptotic notation made explicit
--   - encoding: the reference data chosen arbitrarily → universally quantified; reason: the paper choices are arbitrary
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 17, Corollary 14

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_Packing
import Definitions.Def_StackingStars_Main_ReferenceData
import Definitions.Def_StackingStars_Main_FineType
import Definitions.Def_StackingStars_Main_Bowl

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 17 (PDF 19), Corollary 14. Stars `P i` in the size group with scales `r, w`, star `i` of fine
type `τ i`, and their bowls `Q(P i) = Q_{τ i}(P i)` of Lemma 11. There are translations `t` of
the bowls and rectangles `B_j` (`j < m`) such that every bowl of part `j` has the fine type `τ' j`
of its rectangle and lies in `B_j`; `B_j` has sides parallel to `u_{τ' j}`, `d_{τ' j}` and
dimensions at most `K r × K w`; the bowls of one rectangle have pairwise disjoint interiors and
pairwise disjoint separators (a stack); and `Σ_j |B_j| ≤ K · OPT′(P)`, `K` universal. -/
theorem corollary_14 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (P : Fin n → List Pt), (∀ i, IsStarPolygon (P i)) →
      ∀ (D : ∀ i, RefData (region (P i))) (r w : ℝ), 0 < r → 0 < w →
      (∀ i, (D i).InGroup r w) → ∀ τ : Fin n → FineType, (∀ i, HasFineType r w (D i) (τ i)) →
      ∃ (t : Fin n → Pt) (m : ℕ) (part : Fin n → Fin m) (τ' : Fin m → FineType)
        (p : Fin m → Pt) (a b : Fin m → ℝ),
        (∀ i, τ i = τ' (part i)) ∧
        (∀ j, 0 ≤ a j ∧ a j ≤ K * r ∧ 0 ≤ b j ∧ b j ≤ K * w) ∧
        (∀ i, translate (t i) ((D i).bowl r w (τ i)) ⊆
          rect (p (part i)) ((τ' (part i)).u r w) ((τ' (part i)).d r w) (a (part i))
            (b (part i))) ∧
        (∀ i i', i ≠ i' → part i = part i' →
          Disjoint (interior (translate (t i) ((D i).bowl r w (τ i))))
            (interior (translate (t i') ((D i').bowl r w (τ i')))) ∧
          Disjoint (translate (t i) ((D i).bowlSep r w (τ i)))
            (translate (t i') ((D i').bowlSep r w (τ i')))) ∧
        ∑ j, area (rect (p j) ((τ' j).u r w) ((τ' j).d r w) (a j) (b j)) ≤
          K * optPrime (fun i => region (P i)) := by sorry

end StackingStars.Main
