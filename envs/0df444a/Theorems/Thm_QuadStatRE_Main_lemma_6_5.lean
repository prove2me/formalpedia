-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_6_5
-- name    : QuadStatRE.Main.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:48:00.457384+00:00
-- url     : https://prove2.me/theorems/5d452b87-36ff-4c1a-90ee-03aff44b7427
-- title:
--   Lemma 6.5 — τ(W) ≤ (√Λ_R(W) − 1)/(√8 − 1) for any reference R covering supp(M)
-- statement:
--   Let $W=(W_s)_{s\in G}$ be a leakage family on a finite alphabet $\Omega$ with mixture $M$, and let $R$ be a distribution on $\Omega$ with $\operatorname{supp}(M)\subseteq\operatorname{supp}(R)$. Then
--   $$\tau(W)\le\frac{\sqrt{\Lambda_R(W)}-1}{\sqrt8-1}, \tag{6.7}$$
--   where $\Lambda_R(W)=\frac18\sum_sK_{W,R}(s,s)$ is the average likelihood second moment with respect to $R$.
--
--   The lemma lets the analysis compute a second moment against a convenient product reference instead of the true, correlated mixture.
--
--   Differences from the source:
--
--   - encoding: supp(M) ⊆ supp(R) → M(ω) ≠ 0 → R(ω) ≠ 0 for every ω; reason: support inclusion pointwise
--   - encoding: distributions on a finite set → nonnegative functions Ω → ℝ of total mass one (IsLaw / IsLeakageFamily); reason: finite distributions as probability vectors
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 31, Lemma 6.5, (6.7)

import Mathlib
import Definitions.Def_QuadraticRE_SD
import Definitions.Def_QuadStatRE_Main_ChiSquare
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 6.5 (Bounding normalized `χ²`-information by a second moment), p. 31: for every
finite-output leakage family `W` and reference distribution `R` with `supp(M) ⊆ supp(R)`,
`τ(W) ≤ (√Λ_R(W) − 1)/(√8 − 1)` (6.7). -/
theorem lemma_6_5 {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) (R : Ω → ℝ) (hW : IsLeakageFamily W)
    (hR : IsLaw R) (hsupp : ∀ ω, mix W ω ≠ 0 → R ω ≠ 0) :
    tau W ≤ (Real.sqrt (Lam R W) - 1) / (Real.sqrt 8 - 1) := by sorry

end QuadStatRE.Main
