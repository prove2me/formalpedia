-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_11
-- name    : QTDecode.Parallel.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:07.69262+00:00
-- url     : https://prove2.me/theorems/5ca1d521-d2f1-44ac-81c7-487a9acd2e42
-- title:
--   Lemma 11, p. 15 — ordinary columns and rows cluster: |T| ≤ 64|S_iȷ̄|/(δ²Δ) when |S_iȷ̄| ≤ δ|V₀₀|/4
-- statement:
--   Work in the setting of Lemma 10 (non-bipartite Ramanujan $\mathrm{Cay}(G,A)$, $\mathrm{Cay}(G,B)$; $\kappa$-product-expanding dual tensor code; $x\in\mathcal C_1\setminus\mathcal C_0^\perp$ coset-minimal with minimal representation $(C_0,R_0,C_1,R_1)$), assume moreover that $C_A$ and $C_B$ have minimum distance at least $\delta\Delta$, and call a vertex of $S_{ij}$ ordinary if it is not exceptional for $\alpha=\delta^2/256$. Fix $i,j\in\{0,1\}$ and write $\bar\imath=1-i$, $\bar\jmath=1-j$.
--
--   1. Let $T\subseteq V_{ij}$ be the set of vertices whose local views see at least one non-zero $C_A$-codeword of $C_j$ on a column shared with the local view of an ordinary vertex $w\in V_{\bar\imath j}$.
--   2. Let $T'\subseteq S_{\bar\imath\bar\jmath}$ be the set of vertices on whose $Q$-neighbourhood $R_{\bar\imath}$ displays a non-zero row codeword of $C_B$ shared with the local view of an ordinary vertex $w\in S_{\bar\imath j}$.
--
--   If $|S_{i\bar\jmath}|\le\delta|V_{00}|/4$, then
--   $$|T|\le\frac{64}{\delta^2\Delta}\,|S_{i\bar\jmath}|\qquad\text{and}\qquad|T'|\le\frac{64}{\delta^2\Delta}\,|S_{i\bar\jmath}|.$$
--
--   Combined with Lemma 10 this forces the ordinary columns of a low-norm codeword to concentrate on few $Q$-neighbourhoods, producing too many exceptional vertices (proof of Lemma 8).
--
--   **Formalization Note** The column of $Q(v)$ labelled $b$ is shared with the B-neighbour of $v$ across $b$, and the row labelled $a$ with the A-neighbour across $a$ (p. 11). The product-expansion hypothesis is part of the section's setting and is not used by this statement.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 15, Lemma 11 (T defined just before it, p. 15)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 11, p. 15. Setting of §3 (pp. 13–15) as in Lemma 10, with `C_A`, `C_B` of minimum
distance at least `δΔ`; ordinary vertices are the non-exceptional active ones for `α = δ²/256`.
Let `T ⊆ V_ij` be the set of vertices whose local view sees a non-zero `C_A`-codeword of `C_j`
on a column shared with an ordinary vertex `w ∈ V_īj`. If `|S_iȷ̄| ≤ δ|V₀₀|/4`, then
`|T| ≤ 64/(δ²Δ) |S_iȷ̄|`. The same bound holds for the set `T ⊆ S_īȷ̄` of vertices on whose
`Q`-neighbourhood `R_ī` displays a non-zero row codeword of `C_B` shared with an ordinary vertex
`w ∈ S_īj`. -/
theorem lemma_11 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ)
    (hA : A.card = Δ) (hB : B.card = Δ)
    (hAinv : ∀ a ∈ A, a⁻¹ ∈ A) (hBinv : ∀ b ∈ B, b⁻¹ ∈ B)
    (hRamA : IsRamanujanAdj (leftCayleyAdj A) Δ)
    (hnbA : ∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ))
    (hRamB : IsRamanujanAdj (rightCayleyAdj B) Δ)
    (hnbB : ∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ))
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (hdA : HasMinDistAtLeast CA (δ * Δ)) (hdB : HasMinDistAtLeast CB (δ * Δ))
    (hexp : IsProductExpanding CA CB Δ κ)
    (x : G × A × B → ZMod 2) (hx1 : x ∈ qtCode1 CA CB) (hx0 : x ∉ qtSigmaXSpan CA CB)
    (D : Decomp (G × A × B)) (hD : IsRepr CA CB x D)
    (hDmin : ∀ D', IsRepr CA CB x D' → decompNorm D ≤ decompNorm D')
    (hcoset : ∀ y, x + y ∈ qtSigmaXSpan CA CB → ∀ D', IsRepr CA CB y D' →
      decompNorm D ≤ decompNorm D') :
    ∀ i j : Bool, ((activeSet D i (!j)).card : ℝ) ≤ δ * (Fintype.card G : ℝ) / 4 →
      ((colShareSet D (δ ^ 2 / 256) Δ i j).card : ℝ) ≤
          64 / (δ ^ 2 * Δ) * ((activeSet D i (!j)).card : ℝ) ∧
      ((rowShareSet D (δ ^ 2 / 256) Δ (!i) (!j)).card : ℝ) ≤
          64 / (δ ^ 2 * Δ) * ((activeSet D i (!j)).card : ℝ) := by sorry

end QTDecode.Parallel
