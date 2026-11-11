-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_6_1
-- name    : QuadStatRE.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:56.987788+00:00
-- url     : https://prove2.me/theorems/f10977dd-48bc-4fb9-9195-4c4c0c1d8e0a
-- title:
--   Lemma 6.1 — SD(W_s, M) ≤ ½√(7τ(W)) for affine-symmetric leakage families
-- statement:
--   Let $W=(W_s)_{s\in G}$, $G=\mathbb F_2^3$, be an affine-symmetric leakage family on a finite alphabet $\Omega$, with mixture $M=\frac18\sum_sW_s$ and normalized $\chi^2$-information $\tau(W)$. Then for every $s\in G$
--   $$\mathrm{SD}(W_s,M)\le\frac12\sqrt{7\,\tau(W)}.$$
--
--   This converts the scalar $\tau$ into a privacy bound: the leaky simulator run on a sample of $M$ instead of $W_s$ is a simulator with privacy error at most $\frac12\sqrt{7\tau}$.
--
--   Differences from the source:
--
--   - encoding: distributions on a finite set → nonnegative functions Ω → ℝ of total mass one (IsLaw / IsLeakageFamily); reason: finite distributions as probability vectors
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 28, Lemma 6.1

import Mathlib
import Definitions.Def_QuadraticRE_SD
import Definitions.Def_QuadStatRE_Main_ChiSquare
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 6.1 (Normalized `χ²`-information controls privacy), p. 28: for every affine-symmetric
leakage family `W` and every `s ∈ G`, `SD(W_s, M) ≤ (1/2) √(7 τ(W))`. -/
theorem lemma_6_1 {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) (hW : IsLeakageFamily W)
    (hA : AffineSymmetric W) (s : G) :
    SD (W s) (mix W) ≤ 1 / 2 * Real.sqrt (7 * tau W) := by sorry

end QuadStatRE.Main
