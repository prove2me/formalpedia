-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_lemma_17
-- name    : RankOneBimatrix.BinSearch.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:11.834321+00:00
-- url     : https://prove2.me/theorems/1c5d8074-e82c-4ed8-9471-626a02f12365
-- title:
--   Lemma 17, p. 17 — the bracket contains an equilibrium
-- statement:
--   Suppose auxiliary equilibria at the two bracket endpoints have the signs in (38). Then some auxiliary equilibrium within the closed bracket lies on $x^\top a=\lambda$.
--
--   $$\underline\lambda\le x_{\mathrm{lo}}^\top a,\quad x_{\mathrm{hi}}^\top a\le\overline\lambda\Longrightarrow\exists\lambda\in[\underline\lambda,\overline\lambda],\ (\lambda,x,y)\in\mathcal N,\ x^\top a=\lambda.$$
--
--   This is the bisection invariant. **Formalization Note** Both strategy index types are nonempty.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 17, Lemma 17 and (38)

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Lemma 17, p. 17: the bracket invariant (38) meets the hyperplane. -/
theorem lemma_17 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (lo hi : ℝ) (xLo xHi : Fin m → ℝ) (yLo yHi : Fin n → ℝ)
    (horder : lo ≤ hi)
    (hlo : (lo, xLo, yLo) ∈ NSet A b) (hloA : lo ≤ xLo ⬝ᵥ a)
    (hhi : (hi, xHi, yHi) ∈ NSet A b) (hhiA : xHi ⬝ᵥ a ≤ hi) :
    ∃ (lam : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ),
      lo ≤ lam ∧ lam ≤ hi ∧ (lam, x, y) ∈ NSet A b ∧ x ⬝ᵥ a = lam := by sorry

end RankOneBimatrix.BinSearch
