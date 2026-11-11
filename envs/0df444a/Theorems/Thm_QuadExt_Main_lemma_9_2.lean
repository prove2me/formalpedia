-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_9_2
-- name    : QuadExt.Main.lemma_9_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:58.337597+00:00
-- url     : https://prove2.me/theorems/b4590d6e-b080-4a41-8196-57915b3fb351
-- title:
--   Lemma 9.2 — a quadratic source that is not $q$-pure is $O(\varepsilon)$-close to a mixture of affine sources of entropy $q - O(\log(1/\varepsilon))$
-- statement:
--   Let $X = f(U)$ be a quadratic source with generating map $f : \mathbb F_2^{k+\ell} \to \mathbb F_2^n$, $\ell = O(\log(1/\varepsilon))$, and $H^\varepsilon_\infty(X) \ge k$. If $X$ is not $q$-pure, then $X$ is $O(\varepsilon)$-close to a convex combination of affine sources with entropy
--   $$q - O(\log(1/\varepsilon)).$$
--   Precisely: for every constant $A > 0$ there is a constant $B > 0$ such that whenever $\varepsilon > 0$ and $\ell \le A \log_2(1/\varepsilon)$, $X$ is $B\varepsilon$-close to a convex combination of affine sources each of min-entropy at least $q - B\log_2(1/\varepsilon)$. This is the non-pure branch of the win-win analysis of the final extractor.
--
--   Differences from the source:
--   - reading: "can be decomposed is $O(\varepsilon)$ close" → "is $O(\varepsilon)$ close"; reason: garbled sentence, the intended statement is clear.
--   - encoding: $\ell = O(\log(1/\varepsilon))$, $O(\varepsilon)$, $q - O(\log(1/\varepsilon))$ → for every $A > 0$ there is $B > 0$ with $\ell \le A\log_2(1/\varepsilon)$, error $B\varepsilon$ and entropy $q - B\log_2(1/\varepsilon)$; reason: the asymptotic notation made explicit, the hidden constants of the conclusion depending only on that of the hypothesis.
--   - encoding: $\varepsilon > 0$ assumed; $k, \ell$ natural; $q$ real; reason: $\log(1/\varepsilon)$ is undefined at $\varepsilon = 0$.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 31 (PDF 32), Lemma 9.2

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness
import Definitions.Def_QuadExt_Main_Pure

namespace QuadExt.Main

/-- **Lemma 9.2** (p. 31): for every constant `A` in `ℓ = O(log(1/ε))` there is a constant `B` such
that a quadratic source `X = f(U_{k+ℓ})` with `H^ε_∞(X) ≥ k`, `ℓ ≤ A·log₂(1/ε)`, that is not
`q`-pure is `Bε`-close to a convex combination of affine sources with entropy at least
`q − B·log₂(1/ε)`. -/
theorem lemma_9_2 :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
    ∀ (n k ℓ : ℕ) (ε q : ℝ) (f : (Fin (k + ℓ) → ZMod 2) → (Fin n → ZMod 2)),
      0 < ε → (ℓ : ℝ) ≤ A * Real.logb 2 (1 / ε) →
      IsQuadraticMap f → SmoothMinEntropyGE ε (source f) k → ¬ IsPure q f →
      CloseToMixture (B * ε) (source f) fun Q =>
        IsAffineSource Q ∧ q - B * Real.logb 2 (1 / ε) ≤ SSNonExt.minEntropy Q := by sorry

end QuadExt.Main
