-- Prove2me | Theorems.Thm_QTDecode_Parallel_theorem_9
-- name    : QTDecode.Parallel.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:55.383212+00:00
-- url     : https://prove2.me/theorems/4d44caa7-344e-4eed-ac92-c5cbcefab4f0
-- title:
--   Theorem 9, p. 13 (constant corrected: 256 → 1024) — d_min ≥ δ²κ²n/(1024Δ) for Δ large enough
-- statement:
--   Fix $\delta,\kappa>0$. There is $\Delta_0$ such that the following holds for every $\Delta\ge\Delta_0$. Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs. Let the local codes $C_A,C_B$ and their duals $C_A^\perp,C_B^\perp$ all have minimum distance at least $\delta\Delta$, and let both dual tensor codes $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ and $C_A^\perp\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B^\perp$ be $\kappa$-product-expanding. Let $n=|Q|=|G|\Delta^2$. Then every $x\in\mathcal C_1\setminus\mathcal C_0^\perp$ and every $x\in\mathcal C_0\setminus\mathcal C_1^\perp$ satisfies
--   $$|x|\ \ge\ \frac{\delta^2\kappa^2 n}{1024\,\Delta},$$
--   so the quantum Tanner code $(\mathcal C_0,\mathcal C_1)$ has minimum distance $d_{\min}\ge\delta^2\kappa^2n/(1024\Delta)$.
--
--   This is the linear minimum distance of quantum Tanner codes in the quadripartite setting; the decoders' correctness rests on it.
--
--   **Formalization Note** The page prints $\delta^2\kappa^2n/(256\Delta)$. Its proof combines Lemma 8 ($\|x\|\ge\delta^2\kappa n/(512\Delta^2)$) with $|x|\ge\frac{\kappa\Delta}{2}\|x\|$, which gives $1024$, not $256$; the constant is corrected accordingly (the corrected statement is weaker than the printed one). "$\Delta$ large enough" (Theorem 1, p. 4; needed by Lemma 8) is the quantifier $\exists\Delta_0$. $\mathcal C_0^\perp$ is the span of the $\sigma_x$-generators ($C_A\otimes C_B$ on $V_0$) and $\mathcal C_1^\perp$ the span of the $\sigma_z$-generators ($C_A^\perp\otimes C_B^\perp$ on $V_1$).
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 13, Theorem 9 (proof pp. 13–14; = Theorem 1, p. 4)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Theorem 9, p. 13, with the constant corrected from `256` to `1024` (Lemma 8's `512` and the
proof's `|x| ≥ (κΔ/2)‖x‖` give `1024`), and "`Δ` large enough" (Theorem 1, p. 4) made explicit.
For every `δ, κ > 0` there is `Δ₀` such that for `Δ ≥ Δ₀`, non-bipartite Ramanujan `Cay(G, A)`,
`Cay(G, B)`, local codes `C_A`, `C_B` and their duals of minimum distance at least `δΔ`, and both
dual tensor codes `κ`-product-expanding: every `x ∈ 𝒞₁ ∖ 𝒞₀^⊥` and every `x ∈ 𝒞₀ ∖ 𝒞₁^⊥` has
weight `|x| ≥ δ²κ²n/(1024Δ)`, `n = |Q|`; hence `d_min ≥ δ²κ²n/(1024Δ)`. -/
theorem theorem_9 :
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
      HasMinDistAtLeast (codeDual CA) (δ * Δ) → HasMinDistAtLeast (codeDual CB) (δ * Δ) →
      IsProductExpanding CA CB Δ κ → IsProductExpanding (codeDual CA) (codeDual CB) Δ κ →
      (∀ x ∈ qtCode1 CA CB, x ∉ qtSigmaXSpan CA CB →
        δ ^ 2 * κ ^ 2 * (Fintype.card (G × A × B) : ℝ) / (1024 * Δ) ≤ (hammingNorm x : ℝ)) ∧
      (∀ x ∈ qtCode0 CA CB, x ∉ sigmaZSpan CA CB →
        δ ^ 2 * κ ^ 2 * (Fintype.card (G × A × B) : ℝ) / (1024 * Δ) ≤ (hammingNorm x : ℝ)) := by sorry

end QTDecode.Parallel
