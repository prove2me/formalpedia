-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_6_7
-- name    : QuadStatRE.Main.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:48:05.910554+00:00
-- url     : https://prove2.me/theorems/20306d41-93f0-4027-b1f2-0f963811af37
-- title:
--   Lemma 6.7 — cubic contraction τ(A(W)) ≤ 113 τ(W)³ once τ(W) ≤ 1/16
-- statement:
--   For every affine-symmetric leakage family $W$ on a finite alphabet with $\tau(W)\le1/16$,
--   $$\tau(\mathcal A(W))\le113\,\tau(W)^3 .$$
--
--   Once the leakage enters this regime, $\tau$ decays doubly exponentially in the number of RM steps; this drives the privacy bound of Theorem 5.2.
--
--   Differences from the source:
--
--   - encoding: distributions on a finite set → nonnegative functions Ω → ℝ of total mass one (IsLaw / IsLeakageFamily); reason: finite distributions as probability vectors
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 32, Lemma 6.7

import Mathlib
import Definitions.Def_QuadStatRE_Main_ChiSquare
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 6.7 (Cubic contraction of normalized `χ²`-information), p. 32: for every affine-symmetric
leakage family `W` with `τ(W) ≤ 1/16`, `τ(A(W)) ≤ 113 τ(W)³`. -/
theorem lemma_6_7 {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) (hW : IsLeakageFamily W)
    (hA : AffineSymmetric W) (hτ : tau W ≤ 1 / 16) :
    tau (amp W) ≤ 113 * tau W ^ 3 := by sorry

end QuadStatRE.Main
