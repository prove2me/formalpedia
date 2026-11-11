-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_proposition_B_1
-- name    : PriceCapacities.LowerBound.proposition_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:22:13.748922+00:00
-- url     : https://prove2.me/theorems/0759ea1e-8e64-4e80-a8c9-52f476691543
-- title:
--   Proposition B.1 — parities form an orthonormal basis; Fourier expansion and Parseval's identity
-- statement:
--   Let $d\ge0$ and let $F_d$ be the space of real functions on $\{-1,1\}^d$ with $\langle g,h\rangle=2^{-d}\sum_yg(y)h(y)$. The parity functions $\{\chi_S:S\subseteq[d]\}$ form an orthonormal basis of $F_d$: $\langle\chi_S,\chi_T\rangle=1$ if $S=T$ and $0$ otherwise, and every $g\in F_d$ has the Fourier expansion
--   $$g(y)=\sum_{S\subseteq[d]}\hat g(S)\chi_S(y)\qquad\text{for all }y,$$
--   whose coefficients are unique (any expansion $g=\sum_Sc_S\chi_S$ has $c_S=\hat g(S)$), and Parseval's identity
--   $$\|g\|_2^2=\sum_{S\subseteq[d]}\hat g(S)^2$$
--   holds. This is the basic coordinate system used to compute the eigenvalues in the proof of Lemma 10.6.
--
--   Differences from the source:
--
--   - encoding: {−1,1}^d and F_d → Cube d = Fin d → ℤˣ and functions Cube d → ℝ; reason: ℤˣ = {1, −1}
--   - encoding: the parities form an orthonormal basis of F_d → ⟨χ_S, χ_T⟩ = [S = T] for all S, T, together with the expansion of every g (spanning) and uniqueness of its coefficients; reason: an orthonormal family that spans is an orthonormal basis
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 61, Proposition B.1

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_Fourier

namespace PriceCapacities.LowerBound

theorem proposition_B_1 (d : ℕ) :
    (∀ S T : Finset (Fin d), cubeInner (parity S) (parity T) = if S = T then 1 else 0) ∧
    ∀ g : Cube d → ℝ,
      (∀ y, g y = ∑ S : Finset (Fin d), fourierCoeff g S * parity S y) ∧
      (∀ c : Finset (Fin d) → ℝ, (∀ y, g y = ∑ S : Finset (Fin d), c S * parity S y) →
        c = fourierCoeff g) ∧
      cubeNorm g ^ 2 = ∑ S : Finset (Fin d), fourierCoeff g S ^ 2 := by sorry

end PriceCapacities.LowerBound
