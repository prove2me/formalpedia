-- Prove2me | Theorems.Thm_QuadExt_Main_corollary_5_2
-- name    : QuadExt.Main.corollary_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:47.038931+00:00
-- url     : https://prove2.me/theorems/28f91511-cf8b-4d7e-86aa-b321a581312b
-- title:
--   Corollary 5.2 — a $(t-\ell-1)$-pure quadratic source is $\varepsilon$-close to a mixture of high-derivative-entropy subsources
-- statement:
--   Let $X = f(Y, Z)$ be a quadratic source with generating map $f : \mathbb F_2^{k+\ell} \to \mathbb F_2^n$, $Y = U_s$, $Z = U_{k+\ell-s}$, and $H^{\varepsilon^3}_\infty(X) \ge k$. Let $r, t$ satisfy $rt \le s/2$ and suppose $X$ is $(t - \ell - 1)$-pure. Then $X$ is $\varepsilon$-close to a convex combination of subsources
--   $$X' = g(Y', Z) = g_1(Y') + g_2(Y', Z) + g_3(Z)$$
--   with (1) $H_\infty(\partial_a g_1(Y')) \ge r$ for all $a \ne 0$, (2) $H^{\varepsilon^2}_\infty(X') \ge s' + |Z| - \ell$, (3) $Y' = U_{s'}$ with $s' \ge s/2$, and (4) $g_2$ bilinear. Each $X'$ is obtained by restricting $f$ to an affine subspace of the generating bits that leaves $Z$ unchanged. This is the form in which the structure theorem enters the proof of Theorem 7.2.
--
--   Differences from the source:
--   - encoding: generating bits $\mathbb F_2^{k+\ell}$ split as $(Y, Z)$ → `Fin s ⊕ Fin z` with $s + z = k + \ell$; reason: as in Theorem 5.1.
--   - encoding: $X'$ obtained by restricting $f$ to an affine subspace leaving $Z$ unchanged → `source` of $(y', z) \mapsto f(L(y'), z)$ for an injective affine $L : \mathbb F_2^{s'} \to \mathbb F_2^s$; reason: the same subsources.
--   - encoding: $r, t$ → natural numbers with $2rt \le s$; $k, \ell$ natural; purity threshold $t - \ell - 1$ as a real number; reason: integer parameters, and the threshold may be negative.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 19 (PDF 20), Corollary 5.2

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness
import Definitions.Def_QuadExt_Main_Pure

namespace QuadExt.Main

/-- **Corollary 5.2** (p. 19): if moreover `rt ≤ s/2` and `X` is `(t − ℓ − 1)`-pure, then `X` is
`ε`-close to a convex combination of subsources `X′ = g₁(Y′) + g₂(Y′, Z) + g₃(Z)` obtained by
restricting `f` to an affine subspace of the generating bits that leaves `Z` untouched, with
`H_∞(∂_a g₁(Y′)) ≥ r` for all `a ≠ 0`, `H^{ε²}_∞(X′) ≥ s′ + |Z| − ℓ`, `Y′ = U_{s′}`, `s′ ≥ s/2`,
and `g₂` bilinear. -/
theorem corollary_5_2 (n k ℓ s z : ℕ) (hsz : s + z = k + ℓ) (ε : ℝ)
    (f : (Fin s ⊕ Fin z → ZMod 2) → (Fin n → ZMod 2)) (hf : IsQuadraticMap f)
    (hX : SmoothMinEntropyGE (ε ^ 3) (source f) k)
    (r t : ℕ) (hrt : 2 * (r * t) ≤ s) (hpure : IsPure ((t : ℝ) - ℓ - 1) f) :
    CloseToMixture ε (source f) fun Q =>
      ∃ (s' : ℕ) (L : (Fin s' → ZMod 2) → (Fin s → ZMod 2)),
          IsInjAffine L ∧ s ≤ 2 * s' ∧
          (∃ (g₁ : (Fin s' → ZMod 2) → (Fin n → ZMod 2))
              (g₂ : (Fin s' → ZMod 2) → (Fin z → ZMod 2) → (Fin n → ZMod 2))
              (g₃ : (Fin z → ZMod 2) → (Fin n → ZMod 2)),
            IsBilinear g₂ ∧ (∀ y w, f (join (L y) w) = g₁ y + g₂ y w + g₃ w) ∧
            ∀ a : Fin s' → ZMod 2, a ≠ 0 → (r : ℝ) ≤ SSNonExt.minEntropy (source (dirDeriv a g₁))) ∧
          Q = source (fun x : Fin s' ⊕ Fin z → ZMod 2 =>
            f (join (L fun i => x (Sum.inl i)) fun j => x (Sum.inr j))) ∧
          SmoothMinEntropyGE (ε ^ 2) Q ((s' : ℝ) + z - ℓ) := by sorry

end QuadExt.Main
