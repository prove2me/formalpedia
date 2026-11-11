-- Prove2me | Theorems.Thm_QuadExt_Main_theorem_5_1
-- name    : QuadExt.Main.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:54.05233+00:00
-- url     : https://prove2.me/theorems/2ac17295-16bd-41e3-9e59-2aeefcef08fb
-- title:
--   Theorem 5.1 — structure theorem: a quadratic source is $\varepsilon$-close to a mixture of affine pieces or high-derivative-entropy pieces, $Z$ untouched
-- statement:
--   Let $X = f(Y, Z)$ be a quadratic source with generating map $f : \mathbb F_2^{k+\ell} \to \mathbb F_2^n$, where the generating bits split as $Y = U_s$ and $Z = U_{k+\ell-s}$, and suppose $H^{\varepsilon^3}_\infty(X) \ge k$. Let $r, t$ be positive integers with $rt \le s$. Then $X$ is $\varepsilon$-close to a convex combination of subsources $f(U_V)$, $V$ an affine subspace of $\mathbb F_2^{k+\ell}$, each of one of two types:
--
--   1. an affine source ($f|_V$ affine) with $H_\infty \ge t - \ell - 1$; or
--   2. a source $W(Y', Z) = g_1(Y') + g_2(Y', Z) + g_3(Z)$ with $Y' = U_{s'}$, $s' \ge s - rt$, $g_2$ bilinear, and
--   $$H_\infty\big(\partial_a g_1(Y')\big) \ge r \ \text{ for all } a \ne 0, \qquad H^{\varepsilon^2}_\infty\big(W(Y', Z)\big) \ge s' + |Z| - \ell,$$
--   where $Z$ is the same seed as in $X$ and is independent of $Y'$ (the subspace is $V = A' \times \mathbb F_2^{|Z|}$).
--
--   This dichotomy (affine pieces versus pieces of high derivative entropy) is the entry point of the paper's analysis of quadratic sources.
--
--   Differences from the source:
--   - encoding: generating bits $\mathbb F_2^{k+\ell}$ with $Y$ the first $s$ coordinates → `Fin s ⊕ Fin z → ZMod 2` with $s + z = k + \ell$; reason: same bits, with the $(Y, Z)$ split made explicit.
--   - encoding: $f(U_V)$ for an affine subspace $V$ → `source (f ∘ L)` for an injective affine $L$ with image $V$; for type 2, $L$ acts on the $Y$ block only and $Z$ is passed through; reason: every non-empty affine subspace is such an image, and this is how "$Z$ is the same seed, independent of $Y'$" is expressed.
--   - encoding: $k, \ell$ → natural numbers; reason: $k + \ell$ is a number of generating bits.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 18 (PDF 19), Theorem 5.1

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness

namespace QuadExt.Main

/-- **Theorem 5.1** (structure theorem, p. 18): a quadratic source `X = f(Y, Z)` on `k + ℓ`
generating bits (`Y = U_s`, `Z = U_{k+ℓ−s}`) with `H^{ε³}_∞(X) ≥ k` is `ε`-close to a convex
combination of subsources `f(U_V)`, `V` an affine subspace of the generating bits, each either
(1) an affine source of min-entropy at least `t − ℓ − 1` (`f|_V` affine), or (2) of the form
`g₁(Y′) + g₂(Y′, Z) + g₃(Z)` with `Y′ = U_{s′}`, `s′ ≥ s − rt`, `g₂` bilinear,
`H_∞(∂_a g₁(Y′)) ≥ r` for all `a ≠ 0`, `H^{ε²}_∞ ≥ s′ + |Z| − ℓ`, and `Z` the same seed as in `X`. -/
theorem theorem_5_1 (n k ℓ s z : ℕ) (hsz : s + z = k + ℓ) (ε : ℝ)
    (f : (Fin s ⊕ Fin z → ZMod 2) → (Fin n → ZMod 2)) (hf : IsQuadraticMap f)
    (hX : SmoothMinEntropyGE (ε ^ 3) (source f) k)
    (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (hrt : r * t ≤ s) :
    CloseToMixture ε (source f) fun Q =>
      (∃ (s' : ℕ) (L : (Fin s' → ZMod 2) → (Fin s ⊕ Fin z → ZMod 2)),
          IsInjAffine L ∧ IsAffineMap (f ∘ L) ∧ Q = source (f ∘ L) ∧
          (t : ℝ) - ℓ - 1 ≤ SSNonExt.minEntropy Q) ∨
      (∃ (s' : ℕ) (L : (Fin s' → ZMod 2) → (Fin s → ZMod 2)),
          IsInjAffine L ∧ (s : ℤ) - r * t ≤ s' ∧
          (∃ (g₁ : (Fin s' → ZMod 2) → (Fin n → ZMod 2))
              (g₂ : (Fin s' → ZMod 2) → (Fin z → ZMod 2) → (Fin n → ZMod 2))
              (g₃ : (Fin z → ZMod 2) → (Fin n → ZMod 2)),
            IsBilinear g₂ ∧ (∀ y w, f (join (L y) w) = g₁ y + g₂ y w + g₃ w) ∧
            ∀ a : Fin s' → ZMod 2, a ≠ 0 → (r : ℝ) ≤ SSNonExt.minEntropy (source (dirDeriv a g₁))) ∧
          Q = source (fun x : Fin s' ⊕ Fin z → ZMod 2 =>
            f (join (L fun i => x (Sum.inl i)) fun j => x (Sum.inr j))) ∧
          SmoothMinEntropyGE (ε ^ 2) Q ((s' : ℝ) + z - ℓ)) := by sorry

end QuadExt.Main
