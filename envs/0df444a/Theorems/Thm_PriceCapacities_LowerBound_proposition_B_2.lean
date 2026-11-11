-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_proposition_B_2
-- name    : PriceCapacities.LowerBound.proposition_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:22:27.869387+00:00
-- url     : https://prove2.me/theorems/0e356c9a-0c1f-4a94-9e20-6c107f226bb6
-- title:
--   Proposition B.2 — even functions have no odd-level coefficients; symmetric functions have level-dependent coefficients
-- statement:
--   Let $g:\{-1,1\}^d\to\mathbb R$.
--
--   (i) If $g(-y)=g(y)$ for every $y$, then $\hat g(S)=0$ for every $S\subseteq[d]$ with $|S|$ odd.
--
--   (ii) If $g$ is invariant under coordinate permutations, i.e. $g(y_{\pi(1)},\dots,y_{\pi(d)})=g(y)$ for every permutation $\pi$ of $[d]$ and every $y$, then $\hat g(S)$ depends only on $|S|$: $\hat g(S)=\hat g(T)$ whenever $|S|=|T|$.
--
--   These symmetries of $g(y)=|\sum_j y_j|$-type functions reduce the spectrum computed in Lemma 10.6 to one eigenvalue per even level.
--
--   Differences from the source:
--
--   - encoding: g(−y), invariance under coordinate permutations → g (−y) with pointwise negation; g (y ∘ π) = g y for every π : Equiv.Perm (Fin d); reason: same conditions
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 61, Proposition B.2

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_Fourier

namespace PriceCapacities.LowerBound

theorem proposition_B_2 (d : ℕ) (g : Cube d → ℝ) :
    ((∀ y, g (-y) = g y) → ∀ S : Finset (Fin d), Odd S.card → fourierCoeff g S = 0) ∧
    ((∀ (π : Equiv.Perm (Fin d)) (y : Cube d), g (y ∘ π) = g y) →
      ∀ S T : Finset (Fin d), S.card = T.card → fourierCoeff g S = fourierCoeff g T) := by sorry

end PriceCapacities.LowerBound
