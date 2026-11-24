-- Prove2me | Theorems.Thm_SurelyBetter_CLB_Supplement_theorem_5
-- name    : SurelyBetter.CLB.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:51:25.728762+00:00
-- url     : https://prove2.me/theorems/dfe0a2f4-83a3-4c53-a927-47f6285535c6
-- title:
--   Theorem 5, p. 7633 (corrected: R ⊆ H(z)) — monotonicity in optimal mixtures on F^{E,F,z,h} implies the slope-ratio bound (17) for every support configuration
-- statement:
--   Let $S$ be a finite set of states and let a preference be MBA, represented by $V\big((u(f(s)))_{s\in S}\big)$ as in (6) with $U=u(X)$ convex and $V$ normalized, monotone and continuous. Fix events $E,F\subseteq S$ with $E\setminus F$ and $F\setminus E$ nonempty, a lottery $z$ with utility $u(z)\in U$, and acts $h,k$ that are interior and belong to $\mathcal F^{E,F,z,h}$ (Definition 3). Write $(h_a,h_b)=(u(h(E\setminus F)),u(h(F\setminus E)))$ and $(k_a,k_b)=(u(k(E\setminus F)),u(k(F\setminus E)))$, and suppose
--   $$k(E\setminus F)\succsim h(E\setminus F)\quad\text{and}\quad h(F\setminus E)\succsim k(F\setminus E),$$
--   that is, $h_a\le k_a$ and $k_b\le h_b$. If the preference satisfies monotonicity in optimal mixtures restricted to $\mathcal F^{E,F,z,h}$, then for every support configuration $(R,l_h,l_k)$ (Definition 5) with $R=[a_0,a_1]\times[b_0,b_1]$, the lines $l_h$ and $l_k$ are not vertical and
--   $$\frac{\mathrm{Slope}(l_h)}{\mathrm{Slope}(l_k)}\le\frac{u(k(E\setminus F))-\min_{r\in R}r(E\setminus F)}{u(h(E\setminus F))-\min_{r\in R}r(E\setminus F)}\times\frac{u(h(F\setminus E))-\min_{r\in R}r(F\setminus E)}{u(k(F\setminus E))-\min_{r\in R}r(F\setminus E)},\tag{17}$$
--   where $\min_{r\in R}r(E\setminus F)=a_0$ and $\min_{r\in R}r(F\setminus E)=b_0$.
--
--   The bound limits how convex the preference's indifference curves can be on two-dimensional slices of utility space: preferences must be everywhere at most as convex as Cobb–Douglas there. Combined with Theorem 1, violations of the bound translate into nonmonotone responses of a sales agent to compensation.
--
--   **Formalization Note** Acts are utility profiles with values in $U$; $z$ enters only through $u(z)\in U$. The coordinates $h_a,h_b,k_a,k_b$ are named by hypotheses saying that the profiles of $h$ and $k$ take these values on $E\setminus F$ and $F\setminus E$. A support configuration is given by the rectangle's corners $a_0,a_1,b_0,b_1$ and by a point and a nonzero direction for each line; its slope is the ratio of the direction's coordinates. The conclusion that both lines are non-vertical makes the slopes in (17) well defined; the paper's proof derives that both slopes are negative and finite. The standing assumption that $u(X)$ has two distinct points is implied by the interiority of $h$ and is not repeated.
--
--   Differences from the source:
--   - encoding: acts h, k, the lottery z and the MBA representation (6) → utility profiles with values in a convex U, u(z) ∈ U, and IsMBA U V; reason: within the MBA class only utility profiles matter (p. 7624); same instances
--   - correction: Definition 5, "a rectangle R ⊆ H(z) × H(z)" → R = [a₀,a₁] × [b₀,b₁] ⊆ H(z); reason: typo; R consists of points (q(E \ F), q(F \ E)) (Definition 5's own description of its edges) and H(z) is already a set of such pairs (Definition 4, p. 7632), so R ⊆ H(z) is the only well-typed reading; no case is excluded
--   - reading: "Slope(l_h)", "Slope(l_k)" in (17) → the conclusion also states that l_h and l_k are non-vertical, with Slope = d₂/d₁ for a direction d; reason: (17) presupposes finite slopes, and the proof on p. 7634 derives that both are negative and finite from the hypotheses
--   - reading: a rectangle with left and bottom edges and minima min_{r∈R} r(·) → a closed axis-parallel rectangle with a₀ < a₁ and b₀ < b₁; reason: the edges and minima in Definition 5 and Figure 4 presuppose it; its interior contains (h_a, h_b)
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7633, Theorem 5, (17) (Definitions 3–5, pp. 7632–7633)

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Definitions.Def_SurelyBetter_CLB_Supplement_Family
import Definitions.Def_SurelyBetter_CLB_Supplement_SupportConfig

namespace SurelyBetter.CLB.Supplement
open SurelyBetter.CLB
theorem theorem_5 {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (V : (S → ℝ) → ℝ) (hV : IsMBA U V) (E F : Set S)
    (hEF : (E \ F).Nonempty) (hFE : (F \ E).Nonempty) (uz : ℝ) (huz : uz ∈ U)
    (hp kp : S → ℝ) (hh : hp ∈ famF U E F uz hp) (hk : kp ∈ famF U E F uz hp)
    (hh_int : IsInteriorProfile U hp) (hk_int : IsInteriorProfile U kp)
    (ha hb ka kb : ℝ) (hha : ∀ t ∈ E \ F, hp t = ha) (hhb : ∀ t ∈ F \ E, hp t = hb)
    (hka : ∀ t ∈ E \ F, kp t = ka) (hkb : ∀ t ∈ F \ E, kp t = kb)
    (hord_EF : ha ≤ ka) (hord_FE : kb ≤ hb)
    (hMOM : MOMOn V (famF U E F uz hp)) :
    ∀ a₀ a₁ b₀ b₁ : ℝ, ∀ ph dh pk dk : ℝ × ℝ,
      IsSupportConfig U V E F uz hp kp ha hb ka kb a₀ a₁ b₀ b₁ ph dh pk dk →
        dh.1 ≠ 0 ∧ dk.1 ≠ 0 ∧
          slope dh / slope dk ≤ (ka - a₀) / (ha - a₀) * ((hb - b₀) / (kb - b₀)) := by sorry
end SurelyBetter.CLB.Supplement
