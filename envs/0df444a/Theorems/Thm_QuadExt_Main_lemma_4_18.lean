-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_4_18
-- name    : QuadExt.Main.lemma_4_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:45.208322+00:00
-- url     : https://prove2.me/theorems/e7603292-86f8-4546-965a-9db078e5687e
-- title:
--   Lemma 4.18 — weak-injectivity preservation: a size-biased random cell $S$ keeps $H^{\varepsilon/\delta}_\infty(f(U_S)) \ge \log|S| - \ell$ w.p. $1-\delta$
-- statement:
--   Let $f : \mathbb F_2^{k+\ell} \to \mathbb F_2^n$ be any map such that $X = f(U_{k+\ell})$ has $H^\varepsilon_\infty(X) \ge k$. Let $\mathcal S$ be a distribution over subsets of $\mathbb F_2^{k+\ell}$ whose support is a partition of $\mathbb F_2^{k+\ell}$ and which picks each cell $s$ of the partition with probability $|s| / 2^{k+\ell}$. Then for every $\delta > 0$,
--   $$\Pr_{S \sim \mathcal S}\Big[ H^{\varepsilon/\delta}_\infty\big(f(U_S)\big) \ge \log_2 |S| - \ell \Big] \ge 1 - \delta .$$
--   In words: restricting the generating bits of a source with near-full smooth min-entropy to a random cell of a partition, chosen proportionally to its size, loses at most $\ell$ bits relative to the cell size, with high probability. The structure theorem (Theorem 5.1) uses it to bound the entropy of the pieces of its decomposition.
--
--   Differences from the source:
--   - encoding: "with probability $1-\delta$" → probability at least $1 - \delta$, with $\delta > 0$ assumed; reason: $\varepsilon/\delta$ is undefined at $\delta = 0$ and a probability at least $1 - \delta > 1$ is meaningless for $\delta < 0$.
--   - encoding: $\mathcal S$ a distribution over subsets → a `PMF` on `Finset (𝔽₂^{k+ℓ})` whose support is pairwise disjoint and covers $\mathbb F_2^{k+\ell}$; reason: the same partition condition; cells in the support are non-empty because their probability $|s|/2^{k+\ell}$ is positive.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 16 (PDF 17), Lemma 4.18

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Closeness

namespace QuadExt.Main

/-- **Lemma 4.18** (weak-injectivity preservation, p. 16): if `H^ε_∞(f(U_{k+ℓ})) ≥ k` and `S` is a
random cell of a partition of `𝔽₂^{k+ℓ}` drawn with probability proportional to its size, then with
probability at least `1 − δ`, `H^{ε/δ}_∞(f(U_S)) ≥ log₂|S| − ℓ`. -/
theorem lemma_4_18 (n k ℓ : ℕ) (ε δ : ℝ) (hδ : 0 < δ)
    (f : (Fin (k + ℓ) → ZMod 2) → (Fin n → ZMod 2))
    (hX : SmoothMinEntropyGE ε (source f) k)
    (𝒮 : PMF (Finset (Fin (k + ℓ) → ZMod 2)))
    (hdisj : ∀ s ∈ 𝒮.support, ∀ s' ∈ 𝒮.support, s ≠ s' → Disjoint s s')
    (hcover : ∀ x : Fin (k + ℓ) → ZMod 2, ∃ s ∈ 𝒮.support, x ∈ s)
    (hprob : ∀ s ∈ 𝒮.support, (𝒮 s).toReal = (s.card : ℝ) / 2 ^ (k + ℓ)) :
    1 - δ ≤ prob 𝒮 (fun S =>
      SmoothMinEntropyGE (ε / δ) ((unifOn S).map f) (Real.logb 2 S.card - ℓ)) := by sorry

end QuadExt.Main
