-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_14
-- name    : QTDecode.Parallel.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:18.270529+00:00
-- url     : https://prove2.me/theorems/bf06a8aa-db1a-45f6-9edb-013adba4aad6
-- title:
--   Lemma 14, p. 21 — a stalled sequential decoder: |x_v ∩ (C_ȷ̄ + R_ı̄)| ≥ (ε/2)|x_v| and, on ordinary columns, ≥ (ε/4)|y_v|
-- statement:
--   Let $Z=C_0+R_0+C_1+R_1$ be a minimum decomposition of a mismatch vector $Z$ (columns of $C_j$ in $C_A$, rows of $R_i$ in $C_B$), let $C_A$ have minimum distance at least $\delta\Delta$ ($|A|=|B|=\Delta$, $\delta>0$), let $\varepsilon\in(0,1)$, and assume that the sequential decoder of parameter $\varepsilon$ is stalled at $Z$: no vertex $v$ and no non-zero dual tensor codeword $x$ on $Q(v)$ satisfy $|Z|-|Z+x|\ge(1-\varepsilon)|x|$. Write $\bar\imath=1-i$, $\bar\jmath=1-j$ and $\alpha=\delta^2\varepsilon^2/2^{10}$.
--
--   1. For every active vertex $v\in S_{ij}$ and every dual tensor codeword $x_v$ whose support is contained in the restriction of $C_j+R_i$ to $Q(v)$, we have
--   $$|x_v\cap(C_{\bar\jmath}+R_{\bar\imath})|\ \ge\ \frac{\varepsilon}{2}\,|x_v|.$$
--   2. For every ordinary vertex $v\in S_{ij}$ (one with $\|c_v\|+\|r_v\|<\alpha\Delta$) and every column of $Q(v)$ on which $C_j$ is non-zero, the subvector $y_v$ of $C_j$ supported by that column satisfies
--   $$|y_v\cap(C_{\bar\jmath}+R_{\bar\imath})|\ \ge\ \frac{\varepsilon}{4}\,|y_v|.$$
--
--   These overlaps are the edges counted in Lemmas 15 and 16, which lead to the contradiction proving Theorem 12.
--
--   **Formalization Note** Intersections are taken inside $Q(v)$ through the local views, and $|y\cap z|$ counts the coordinates where both are non-zero. The minimum decomposition is the standing assumption of §5.1.1 (p. 21).
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 21, Lemma 14 (setting §5.1.1, p. 21; α = δ²ε²/2¹⁰)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 14, p. 21. Setting of §5.1.1 (p. 21): `D = (C₀, R₀, C₁, R₁)` is a minimum decomposition of
the mismatch `Z`, `C_A` has minimum distance at least `δΔ`, `α = δ²ε²/2¹⁰`, and the sequential
decoder of parameter `ε ∈ (0, 1)` is stalled at `Z`. Then
1. for every active `v ∈ S_ij` and every dual tensor codeword `x_v` supported inside the
   restriction of `C_j + R_i` to `Q(v)`, we have `|x_v ∩ (C_ȷ̄ + R_ı̄)| ≥ (ε/2)|x_v|`;
2. for every ordinary `v ∈ S_ij` and every column `b` of `Q(v)` on which `C_j` is non-zero, the
   subvector `y_v` of `C_j` supported by that column satisfies `|y_v ∩ (C_ȷ̄ + R_ı̄)| ≥ (ε/4)|y_v|`.

Intersections are taken on `Q(v)` (local views). -/
theorem lemma_14 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hA : A.card = Δ) (hB : B.card = Δ)
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (hdA : HasMinDistAtLeast CA (δ * Δ))
    (Z : G × A × B → ZMod 2) (D : Decomp (G × A × B)) (hD : IsMinDecomp CA CB Z D)
    (hstall : IsStalled CA CB ε Z) :
    (∀ (i j : Bool) (g : G), g ∈ activeSet D i j →
      ∀ x : A × B → ZMod 2, x ∈ dualTensorCode CA CB →
        (∀ ab : A × B, x ab ≠ 0 → qtLocalView (D.C j + D.R i) (g, (i, j)) ab ≠ 0) →
        ε / 2 * (hammingNorm x : ℝ) ≤
          (interWeight x (qtLocalView (D.C (!j) + D.R (!i)) (g, (i, j))) : ℝ)) ∧
    (∀ (i j : Bool) (g : G) (b : B), IsOrdinary D (δ ^ 2 * ε ^ 2 / 2 ^ 10) Δ (g, (i, j)) →
      (∃ a : A, qtLocalView (D.C j) (g, (i, j)) (a, b) ≠ 0) →
      ε / 4 * (hammingNorm (fun ab : A × B =>
          if ab.2 = b then qtLocalView (D.C j) (g, (i, j)) ab else 0) : ℝ) ≤
        (interWeight (fun ab : A × B => if ab.2 = b then qtLocalView (D.C j) (g, (i, j)) ab else 0)
          (qtLocalView (D.C (!j) + D.R (!i)) (g, (i, j))) : ℝ)) := by sorry

end QTDecode.Parallel
