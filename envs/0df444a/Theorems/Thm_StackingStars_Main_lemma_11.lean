-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_11
-- name    : StackingStars.Main.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:46:42.961174+00:00
-- url     : https://prove2.me/theorems/e5bfbcab-4504-4f2a-9b1e-a38207851f70
-- title:
--   Lemma 11 — every star of fine type τ lies in a bowl of height 100w inside a constant dilation of itself
-- statement:
--   Let $P$ be a star with reference data $(q_P,R_P,L_P)$ in the size group with scales $r,w>0$, and let $\tau$ be its fine type. Set $h=100w$. Let $R_Q$ and $L_Q$ be the points of the rays $q_P\to R_P$ and $q_P\to L_P$ with $d_\tau\cdot(R_Q-q_P)=d_\tau\cdot(L_Q-q_P)=h$, and let $Q_\tau(P)=P\cup q_PR_Q\cup q_PL_Q$ (the bowl constructed in the proof). There is a universal constant $\alpha>1$ such that for every such $P$:
--
--   * $Q_\tau(P)$ is a bowl aligned along $(d_\tau,u_\tau)$ with height $h$, kernel point $q_{Q}=q_P$ and arm ends $L_Q,R_Q$;
--   * $$P\subseteq Q_\tau(P)\subseteq q_P+\alpha\,(P-q_P);\qquad(6)$$
--   * $R_Q$ lies on the ray $\overrightarrow{q_PR_P}$ and $L_Q$ on the ray $\overrightarrow{q_PL_P}$;
--   * in coordinates with axes $\{u_\tau,d_\tau\}$ and origin $q_Q$, $R_Q=(ha_Q,h)$ and $L_Q=(hb_Q,h)$ with
--   $$7\,\frac rw\le a_Q\le32\,\frac rw,\qquad-4\,\frac rw\le b_Q\le3\,\frac rw.\qquad(7)$$
--
--   Replacing stars by bowls costs a constant factor $\alpha^2$ in the optimum. The bowls are what stack (Corollary 14).
--
--   Differences from the source:
--   - generalization: there is a bowl Q(P) with the listed properties → the bowl P ∪ q R_Q ∪ q L_Q constructed in the proof (p. 16) has them; reason: naming the witness is stronger and specializes to the existential statement; Corollary 14 refers to this bowl
--   - generalization: P of fine type τ in a size group G_{a,b} of an instance → P with r_P ∈ (r/2, r], w_P ∈ (w/2, w] for any r, w > 0; reason: every size group satisfies this, so the statement specializes to the printed one
--   - encoding: a bowl is a possibly weakly simple star-shaped polygon with specified reference data → IsBowl requires a finite union of finite convex hulls, a kernel point, orthonormal directions and the original reference-point extrema; reason: polygonal regions with a kernel allow the zero-width arms in the paper construction; the extremal conditions are stipulated on p. 14
--   - encoding: q_{Q_τ(P)} = q_P → the kernel point argument of IsBowl is q_P; reason: same statement
--   - reading: fine types for left-side stars → mirrored fine types for right-side stars; reason: the WLOG of p. 11 is a mirror image
--   - encoding: the reference data chosen arbitrarily → universally quantified; reason: the paper choices are arbitrary
--   - reading: star-shaped polygons (convex polygons in Theorem 5) → simple polygons represented by arbitrary real vertex lists, as in IsStarPolygon and IsConvexPolygon; reason: the paper reserves possibly weakly simple for the derived bowls; no convexity is added to star inputs and no coordinate or complexity restriction is imposed
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 15, Lemma 11

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_ReferenceData
import Definitions.Def_StackingStars_Main_FineType
import Definitions.Def_StackingStars_Main_Bowl

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 15 (PDF 17), Lemma 11, for the bowl `Q_τ(P) = P ∪ q R_Q ∪ q L_Q` built in its proof (p. 16).
There is a universal `α > 1` such that for every star `P` of fine type `τ` in the size group with
scales `r, w`, with `h = 100 w`: `Q_τ(P)` is a bowl aligned along `(d_τ, u_τ)` with height `h`,
kernel point `q_P` and arm ends `L_Q`, `R_Q`; `P ⊆ Q_τ(P) ⊆ q_P + α (P − q_P)`; `R_Q` lies on the
ray `q_P → R_P` and `L_Q` on the ray `q_P → L_P`; and in coordinates `(u_τ, d_τ)` centred at
`q_P`, `R_Q = (h a_Q, h)` and `L_Q = (h b_Q, h)` with `7 r/w ≤ a_Q ≤ 32 r/w` and
`−4 r/w ≤ b_Q ≤ 3 r/w`. -/
theorem lemma_11 :
    ∃ α : ℝ, 1 < α ∧ ∀ (V : List Pt), IsStarPolygon V → ∀ (D : RefData (region V)) (r w : ℝ),
      0 < r → 0 < w → D.InGroup r w → ∀ τ : FineType, HasFineType r w D τ →
        IsBowl (D.bowl r w τ) D.q (D.bowlL r w τ) (D.bowlR r w τ) (τ.d r w) (τ.u r w) (100 * w) ∧
        region V ⊆ D.bowl r w τ ∧ D.bowl r w τ ⊆ homothety D.q α (region V) ∧
        D.bowlR r w τ ∈ ray D.q D.R ∧ D.bowlL r w τ ∈ ray D.q D.L ∧
        dot (τ.d r w) (D.bowlR r w τ - D.q) = 100 * w ∧
        dot (τ.d r w) (D.bowlL r w τ - D.q) = 100 * w ∧
        7 * (r / w) ≤ dot (τ.u r w) (D.bowlR r w τ - D.q) / (100 * w) ∧
        dot (τ.u r w) (D.bowlR r w τ - D.q) / (100 * w) ≤ 32 * (r / w) ∧
        -4 * (r / w) ≤ dot (τ.u r w) (D.bowlL r w τ - D.q) / (100 * w) ∧
        dot (τ.u r w) (D.bowlL r w τ - D.q) / (100 * w) ≤ 3 * (r / w) := by sorry

end StackingStars.Main
