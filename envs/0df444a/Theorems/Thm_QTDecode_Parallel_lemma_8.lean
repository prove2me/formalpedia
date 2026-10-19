-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_8
-- name    : QTDecode.Parallel.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:00.280047+00:00
-- url     : https://prove2.me/theorems/66936342-a407-4b33-993d-a42159ee6893
-- title:
--   Lemma 8, p. 13 — every x ∈ 𝒞₁ ∖ 𝒞₀^⊥ has norm ‖x‖ ≥ δ²κn/(512Δ²), for Δ large enough
-- statement:
--   Fix $\delta,\kappa>0$. There is $\Delta_0$ such that the following holds for every $\Delta\ge\Delta_0$. Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs; let $C_A\subseteq\mathbb F_2^A$, $C_B\subseteq\mathbb F_2^B$ have minimum distance at least $\delta\Delta$, with $\kappa$-product-expanding dual tensor code $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$; and let $n=|Q|=|G|\Delta^2$. Then every $x\in\mathcal C_1\setminus\mathcal C_0^\perp$ satisfies
--   $$\|x\|\ \ge\ \frac{\delta^2\kappa n}{512\Delta^2},$$
--   i.e. every representation $x=C_1+R_0=C_0+R_1$ of $x$ has $\|C_0\|+\|R_0\|+\|C_1\|+\|R_1\|\ge\delta^2\kappa n/(512\Delta^2)$.
--
--   A lower bound on the number of local codewords needed to write a non-trivial codeword; with robustness it yields the minimum distance (Theorem 9).
--
--   **Formalization Note** The page states no condition on $\Delta$, but its proof (p. 16) needs "$\Delta$ large enough" ("at least $a|S_{10}|$ for any constant $a<1$ and $\Delta$ large enough"); this is the quantifier $\exists\Delta_0\,\forall\Delta\ge\Delta_0$, with $\Delta_0$ depending on $\delta,\kappa$ only (Theorem 1, p. 4, also says "$\Delta$ large enough"). $\|x\|$ is a minimum, stated as a lower bound for every representation.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 13, Lemma 8 (proof p. 16)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 8, p. 13 (with "`Δ` large enough", used in its proof, p. 16). For every `δ, κ > 0` there is
`Δ₀` such that for `Δ ≥ Δ₀`, non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)` (`|A| = |B| = Δ`,
`A = A⁻¹`, `B = B⁻¹`), local codes `C_A`, `C_B` of minimum distance at least `δΔ` with
`κ`-product-expanding dual tensor code: every `x ∈ 𝒞₁ ∖ 𝒞₀^⊥` has `‖x‖ ≥ δ²κn/(512Δ²)`, i.e.
every representation of `x` has norm at least `δ²κn/(512Δ²)`, `n = |Q| = |G|Δ²`. -/
theorem lemma_8 :
    ∀ δ κ : ℝ, 0 < δ → 0 < κ →
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
      A.card = Δ → B.card = Δ →
      (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) →
      IsRamanujanAdj (leftCayleyAdj A) Δ →
      (∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ)) →
      IsRamanujanAdj (rightCayleyAdj B) Δ →
      (∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ)) →
      ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
      HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
      IsProductExpanding CA CB Δ κ →
      ∀ x ∈ qtCode1 CA CB, x ∉ qtSigmaXSpan CA CB →
      ∀ D : Decomp (G × A × B), IsRepr CA CB x D →
        δ ^ 2 * κ * (Fintype.card (G × A × B) : ℝ) / (512 * (Δ : ℝ) ^ 2) ≤ (decompNorm D : ℝ) := by sorry

end QTDecode.Parallel
