-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_15
-- name    : QTDecode.Parallel.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:29.617096+00:00
-- url     : https://prove2.me/theorems/67e838c1-3ca6-46d2-8844-71fe9068150e
-- title:
--   Lemma 15, p. 22 — exceptional vertices are rare for a stalled decoder: |S^e_ii| ≤ 2⁸|S₀|/(α²κ²ε²Δ²)
-- statement:
--   Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs, and let $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ be $\kappa$-product-expanding ($\kappa>0$). Let $Z=C_0+R_0+C_1+R_1$ be a minimum decomposition of a mismatch $Z$ at which the sequential decoder of parameter $\varepsilon\in(0,1)$ is stalled, and let $\alpha=\delta^2\varepsilon^2/2^{10}$ ($\delta>0$). Let $S_{ij}$ be the active vertices, $S_0=S_{00}\cup S_{11}$, $S_1=S_{01}\cup S_{10}$, and $S^e_{ij}$ the exceptional ones ($\|c_v\|+\|r_v\|\ge\alpha\Delta$). If $|S_{ij}|\le\frac{\alpha\kappa\varepsilon}{4}|V_{00}|$ for all $i,j$, then for $i=0,1$
--   $$|S^e_{ii}|\le\frac{2^8}{\alpha^2\kappa^2\varepsilon^2}\,\frac1{\Delta^2}\,|S_0|\qquad\text{and}\qquad|S^e_{i\bar\imath}|\le\frac{2^8}{\alpha^2\kappa^2\varepsilon^2}\,\frac1{\Delta^2}\,|S_1|.$$
--
--   The decoder analogue of Lemma 10, used in the proof of Theorem 12.
--
--   **Formalization Note** $|V_{00}|=|G|$; the hypothesis is read for all four $i,j$, as the proof uses it.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 22, Lemma 15 (setting §5.1.1, p. 21)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 15, p. 22. Setting of §5.1.1 (p. 21): non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)`,
`κ`-product-expanding `C_A ⊗ F₂^B + F₂^A ⊗ C_B`, a minimum decomposition `D` of the mismatch `Z`, and
the sequential decoder of parameter `ε ∈ (0, 1)` stalled at `Z`. With `α = δ²ε²/2¹⁰`, if every
`|S_ij| ≤ (ακε/4)|V₀₀|`, then for `i = 0, 1`:
`|S^e_ii| ≤ 2⁸/(α²κ²ε²) · (1/Δ²) |S₀|` and `|S^e_iī| ≤ 2⁸/(α²κ²ε²) · (1/Δ²) |S₁|`. -/
theorem lemma_15 {G : Type} [Group G] [Fintype G] [DecidableEq G] (A B : Finset G) (Δ : ℕ)
    (ε δ κ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hκ : 0 < κ)
    (hA : A.card = Δ) (hB : B.card = Δ)
    (hAinv : ∀ a ∈ A, a⁻¹ ∈ A) (hBinv : ∀ b ∈ B, b⁻¹ ∈ B)
    (hRamA : IsRamanujanAdj (leftCayleyAdj A) Δ)
    (hnbA : ∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ))
    (hRamB : IsRamanujanAdj (rightCayleyAdj B) Δ)
    (hnbB : ∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ))
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (hexp : IsProductExpanding CA CB Δ κ)
    (Z : G × A × B → ZMod 2) (D : Decomp (G × A × B)) (hD : IsMinDecomp CA CB Z D)
    (hstall : IsStalled CA CB ε Z)
    (hS : ∀ i j : Bool, ((activeSet D i j).card : ℝ) ≤
      δ ^ 2 * ε ^ 2 / 2 ^ 10 * κ * ε / 4 * (Fintype.card G : ℝ)) :
    ∀ i : Bool,
      ((exceptionalSet D (δ ^ 2 * ε ^ 2 / 2 ^ 10) Δ i i).card : ℝ) ≤
          2 ^ 8 / ((δ ^ 2 * ε ^ 2 / 2 ^ 10) ^ 2 * κ ^ 2 * ε ^ 2) * (1 / (Δ : ℝ) ^ 2) *
            (((activeSet D false false).card : ℝ) + (activeSet D true true).card) ∧
      ((exceptionalSet D (δ ^ 2 * ε ^ 2 / 2 ^ 10) Δ i (!i)).card : ℝ) ≤
          2 ^ 8 / ((δ ^ 2 * ε ^ 2 / 2 ^ 10) ^ 2 * κ ^ 2 * ε ^ 2) * (1 / (Δ : ℝ) ^ 2) *
            (((activeSet D false true).card : ℝ) + (activeSet D true false).card) := by sorry

end QTDecode.Parallel
