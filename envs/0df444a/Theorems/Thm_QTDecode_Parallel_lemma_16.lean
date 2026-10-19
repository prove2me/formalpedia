-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_16
-- name    : QTDecode.Parallel.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:14.267982+00:00
-- url     : https://prove2.me/theorems/51099c8b-d2a6-43bf-ac3e-ff486d05bb23
-- title:
--   Lemma 16, p. 23 — ordinary columns and rows cluster for a stalled decoder: |T| ≤ 256|S_iȷ̄|/(δ²ε²Δ)
-- statement:
--   Let $G$, $A$, $B$ be as in Lemma 15 (non-bipartite Ramanujan Cayley graphs, $|A|=|B|=\Delta$), let $C_A,C_B$ have minimum distance at least $\delta\Delta$, let $Z=C_0+R_0+C_1+R_1$ be a minimum decomposition of a mismatch at which the sequential decoder of parameter $\varepsilon\in(0,1)$ is stalled, and call an active vertex ordinary if $\|c_v\|+\|r_v\|<\alpha\Delta$ with $\alpha=\delta^2\varepsilon^2/2^{10}$. Fix $i,j$ and write $\bar\imath=1-i$, $\bar\jmath=1-j$.
--
--   1. Let $T\subseteq V_{ij}$ be the set of vertices $v$ whose $Q(v)$ contains a column that is an ordinary column (a column carrying a non-zero part of $C_j$) for the neighbouring ordinary vertex $w\in V_{\bar\imath j}$ whose local view shares this very column.
--   2. Let $T'\subseteq S_{\bar\imath\bar\jmath}$ be the set of vertices on whose $Q$-neighbourhood $R_{\bar\imath}$ displays a non-zero row codeword of $C_B$ shared by the local view of an ordinary vertex $w\in S_{\bar\imath j}$.
--
--   If $|S_{i\bar\jmath}|\le\delta\varepsilon|V_{i\bar\jmath}|/8$, then
--   $$|T|\le\frac{256}{\delta^2\varepsilon^2\Delta}\,|S_{i\bar\jmath}|\qquad\text{and}\qquad|T'|\le\frac{256}{\delta^2\varepsilon^2\Delta}\,|S_{i\bar\jmath}|.$$
--
--   The decoder analogue of Lemma 11, used in the proof of Theorem 12.
--
--   **Formalization Note** $|V_{i\bar\jmath}|=|G|$. The shared column (row) is the one labelled $b$ ($a$) in both local views (p. 11).
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 23, Lemma 16 (setting §5.1.1, p. 21)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 16, p. 23. Setting of §5.1.1 (p. 21): non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)`,
`C_A`, `C_B` of minimum distance at least `δΔ`, a minimum decomposition `D` of the mismatch `Z`, the
sequential decoder of parameter `ε ∈ (0, 1)` stalled at `Z`, ordinary vertices for `α = δ²ε²/2¹⁰`.
Let `T ⊆ V_ij` be the set of vertices whose `Q(v)` contains a column that is an ordinary column for
the neighbouring vertex `w ∈ V_īj` sharing it. If `|S_iȷ̄| ≤ δε|V_iȷ̄|/8`, then
`|T| ≤ 256/(δ²ε²Δ) |S_iȷ̄|`. The same bound holds for the set `T ⊆ S_īȷ̄` of vertices on whose
`Q`-neighbourhood `R_ī` displays a non-zero row codeword of `C_B` shared with an ordinary vertex
`w ∈ S_īj`. -/
theorem lemma_16 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hA : A.card = Δ) (hB : B.card = Δ)
    (hAinv : ∀ a ∈ A, a⁻¹ ∈ A) (hBinv : ∀ b ∈ B, b⁻¹ ∈ B)
    (hRamA : IsRamanujanAdj (leftCayleyAdj A) Δ)
    (hnbA : ∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ))
    (hRamB : IsRamanujanAdj (rightCayleyAdj B) Δ)
    (hnbB : ∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ))
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (hdA : HasMinDistAtLeast CA (δ * Δ)) (hdB : HasMinDistAtLeast CB (δ * Δ))
    (Z : G × A × B → ZMod 2) (D : Decomp (G × A × B)) (hD : IsMinDecomp CA CB Z D)
    (hstall : IsStalled CA CB ε Z) :
    ∀ i j : Bool, ((activeSet D i (!j)).card : ℝ) ≤ δ * ε * (Fintype.card G : ℝ) / 8 →
      ((colShareSet D (δ ^ 2 * ε ^ 2 / 2 ^ 10) Δ i j).card : ℝ) ≤
          256 / (δ ^ 2 * ε ^ 2 * Δ) * ((activeSet D i (!j)).card : ℝ) ∧
      ((rowShareSet D (δ ^ 2 * ε ^ 2 / 2 ^ 10) Δ (!i) (!j)).card : ℝ) ≤
          256 / (δ ^ 2 * ε ^ 2 * Δ) * ((activeSet D i (!j)).card : ℝ) := by sorry

end QTDecode.Parallel
