-- Prove2me | Theorems.Thm_WangZahlKakeya_KTCW_le_wolff
-- name    : WangZahlKakeya.KTCW_le_wolff
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T15:03:49.017724+00:00
-- url     : https://prove2.me/theorems/d4fe49d1-326a-40ea-9b88-62dde6af307e
-- title:
--   The Wolff axioms of Theorem 1.2 bound $C_{\mathrm{KT\text{-}CW}}(\mathbb{T})$
-- statement:
--   **The non-clustering hypothesis of Theorem 1.2 controls the Katz--Tao Convex Wolff constant.**
--
--   Suppose every rectangular prism of dimensions $a \times b \times 2$ contains at most $100\,ab\,\delta^{-2}$ tubes of $\mathbb{T}$. Then
--
--   $$C_{\mathrm{KT\text{-}CW}}(\mathbb{T}) \;\le\; M$$
--
--   for an absolute constant $M$. Indeed, for a convex set $W$ one may replace $W$ by $W \cap B(0,1)$ without changing the number of tubes it contains, enclose the latter in a prism of dimensions $a \times b \times 2$ built from its two smallest widths, and compare $ab$ with $|W|$ using the fact that a convex body has volume at least a fixed fraction of the volume of its bounding box.
--
--   This is the step by which Theorem 1.2 becomes a special case of Corollary 1.10.
--
--   **Formalization note.** The source asserts the bound with the explicit constant $1000$; it is formalized here with an unspecified absolute constant $M > 0$, which is what the deduction of Theorem 1.2 from Corollary 1.10 actually requires.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 8, the sentence following Corollary 1.10 (“Theorem 1.2 is now a special case of Corollary 1.10 --- the hypotheses of Theorem 1.2 ensure that $\mathcal{C}_{KT}(\mathbb{T})\le 1000$”), together with Theorem 1.2 on p. 3

import Definitions.Def_WangZahlKakeya_wolff

namespace WangZahlKakeya

theorem KTCW_le_wolff :
    ∃ M > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y →
      (∀ a b : ℝ, 0 < a → 0 < b → ∀ W : Set E3, IsPrismOfDims W ![a, b, 2] →
        (tubeCountIn δ n p v W : ℝ) ≤ 100 * a * b * δ ^ (-2 : ℝ)) →
      KTCW δ n p v ≤ M := by sorry

end WangZahlKakeya
