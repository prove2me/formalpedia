-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_10
-- name    : QTDecode.Parallel.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:10.133437+00:00
-- url     : https://prove2.me/theorems/e83a39ec-8b50-4ec7-8f0d-9706d2289c6f
-- title:
--   Lemma 10, p. 14 — few exceptional vertices in a minimal representation: |S^e_ii| ≤ 64|S₀|/(α²κ²Δ²), |S^e_iī| ≤ 64|S₁|/(α²κ²Δ²)
-- statement:
--   Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs, and let the dual tensor code $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ be $\kappa$-product-expanding ($\kappa>0$). Let $x\in\mathcal C_1\setminus\mathcal C_0^\perp$ attain the minimum norm in its coset $x+\mathcal C_0^\perp$ and let $(C_0,R_0,C_1,R_1)$ be a minimal representation of $x$ (the setting of §3, p. 14). Let $S_{ij}\subseteq V_{ij}$ be the vertices on whose $Q$-neighbourhood $C_j+R_i$ is non-zero, $S_0=S_{00}\cup S_{11}$, $S_1=S_{01}\cup S_{10}$, and, with
--   $$\alpha=\delta^2/256\quad(\delta>0),$$
--   let $S^e_{ij}\subseteq S_{ij}$ be the exceptional vertices, those with $\|c_v\|+\|r_v\|\ge\alpha\Delta$ for the restrictions $c_v,r_v$ of $C_j,R_i$ to $Q(v)$. If $|S_{ij}|\le\frac{\alpha\kappa}{2}|V_{00}|$ for all $i,j$, then for $i=0,1$
--   $$|S^e_{ii}|\le\frac{64}{\alpha^2\kappa^2\Delta^2}\,|S_0|\qquad\text{and}\qquad|S^e_{i\bar\imath}|\le\frac{64}{\alpha^2\kappa^2\Delta^2}\,|S_1|,$$
--   where $\bar\imath=1-i$.
--
--   Exceptional vertices are thus an $O(1/\Delta^2)$ fraction, which is what the proof of Lemma 8 contradicts.
--
--   **Formalization Note** $|V_{00}|=|G|$. The page's hypothesis "$|S_{ij}|\le\ldots$" is read for all four $i,j$, as the proof uses it. The page writes "$c_v$ and $r_v$ are the restrictions to $Q(v)$ of $C_j$ and $R_j$"; the restriction of $R_i$ is meant (rows of $Q(v)$, $v\in V_{ij}$, belong to $R_i$), and $\|c_v\|+\|r_v\|$ is computed with $R_i$.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 14, Lemma 10 (α = δ²/256, S_ij and exceptional vertices defined on p. 14)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 10, p. 14. Setting of §3 (pp. 13–14): non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)`,
`κ`-product-expanding `C_A ⊗ F₂^B + F₂^A ⊗ C_B`; `x ∈ 𝒞₁ ∖ 𝒞₀^⊥` attains the minimum norm in its
coset `x + 𝒞₀^⊥`, and `D = (C₀, R₀, C₁, R₁)` is a minimal representation of `x`. With
`α = δ²/256`, exceptional vertices of `S_ij` are those with `‖c_v‖ + ‖r_v‖ ≥ αΔ`. If every
`|S_ij| ≤ (ακ/2)|V₀₀|`, then for `i = 0, 1`:
`|S^e_ii| ≤ 64/(α²κ²Δ²) |S₀|` and `|S^e_iī| ≤ 64/(α²κ²Δ²) |S₁|`,
where `S₀ = S₀₀ ∪ S₁₁` and `S₁ = S₀₁ ∪ S₁₀`. -/
theorem lemma_10 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ)
    (hA : A.card = Δ) (hB : B.card = Δ)
    (hAinv : ∀ a ∈ A, a⁻¹ ∈ A) (hBinv : ∀ b ∈ B, b⁻¹ ∈ B)
    (hRamA : IsRamanujanAdj (leftCayleyAdj A) Δ)
    (hnbA : ∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ))
    (hRamB : IsRamanujanAdj (rightCayleyAdj B) Δ)
    (hnbB : ∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ))
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (hexp : IsProductExpanding CA CB Δ κ)
    (x : G × A × B → ZMod 2) (hx1 : x ∈ qtCode1 CA CB) (hx0 : x ∉ qtSigmaXSpan CA CB)
    (D : Decomp (G × A × B)) (hD : IsRepr CA CB x D)
    (hDmin : ∀ D', IsRepr CA CB x D' → decompNorm D ≤ decompNorm D')
    (hcoset : ∀ y, x + y ∈ qtSigmaXSpan CA CB → ∀ D', IsRepr CA CB y D' →
      decompNorm D ≤ decompNorm D')
    (hS : ∀ i j : Bool,
      ((activeSet D i j).card : ℝ) ≤ δ ^ 2 / 256 * κ / 2 * (Fintype.card G : ℝ)) :
    ∀ i : Bool,
      ((exceptionalSet D (δ ^ 2 / 256) Δ i i).card : ℝ) ≤
          64 / ((δ ^ 2 / 256) ^ 2 * κ ^ 2 * (Δ : ℝ) ^ 2) *
            (((activeSet D false false).card : ℝ) + (activeSet D true true).card) ∧
      ((exceptionalSet D (δ ^ 2 / 256) Δ i (!i)).card : ℝ) ≤
          64 / ((δ ^ 2 / 256) ^ 2 * κ ^ 2 * (Δ : ℝ) ^ 2) *
            (((activeSet D false true).card : ℝ) + (activeSet D true false).card) := by sorry

end QTDecode.Parallel
