-- Prove2me | Theorems.Thm_PhiSobBayes_fact_A_25
-- name    : PhiSobBayes.fact_A_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:10:35.572244+00:00
-- url     : https://prove2.me/theorems/4e5e3b44-0942-4099-8d38-d9eb92fb13d1
-- title:
--   Fact A.25 — $\Psi$-Sobolev with constant $C$ gives $D_\Psi(\nu K_t\|\mu K_t)\le\frac{Ct}{1+Ct}D_\Psi(\nu\|\mu)$
-- statement:
--   Let $J$ be an open interval and $\Psi:J\to\mathbb R$ smooth with $\Psi''>0$, $1/\Psi''$ concave and $\Psi(1)=0$. Let $\mu$ be a probability measure on $\mathbb R^n$ that satisfies the $\Psi$-Sobolev inequality (1) with constant $C$. Then for every probability measure $\nu\ll\mu$ whose density $d\nu/d\mu$ takes values in $J$, and every $t>0$,
--   $$D_\Psi(\nu K_t\,\|\,\mu K_t)\le\frac{Ct}{1+Ct}\,D_\Psi(\nu\,\|\,\mu).$$
--
--   This is a cited result ([MW25a, Lemma 15]): a $\Psi$-Sobolev inequality makes $\Psi$-divergences contract along the Gaussian channel. In the proof of Theorem 3.1 it is applied to $d\nu/d\mu=f/\mathbb E_\mu f$ and gives the direction (i) ⇒ (ii).
--
--   Differences from the source:
--   - encoding: ν ≪ μ, with D_Ψ(ν‖μ) as in Definition 12 → ν, μ probability measures and dν/dμ ∈ J μ-a.e.; reason: Definition 12 (p.56) defines D_Ψ(ν‖μ) only for such pairs; this also forces 1 ∈ J, which Ψ(1) = 0 presupposes
--   - encoding: D_Ψ(ν‖μ) = 𝔼_μ Ψ(dν/dμ) → phiDiv: ∫⁻ ofReal(Ψ(r) − Ψ′(1)(r − 1)) dμ in [0, ∞]; reason: equal to 𝔼_μ Ψ(r) whenever it is defined, since 𝔼_μ(r − 1) = 0; avoids a junk value 0 for an infinite divergence
--   - encoding: Ψ : J → ℝ → Ψ : ℝ → ℝ with AdmissiblePhi J Ψ; reason: Lean functions are total; only the values on J (and Ψ′(1), 1 ∈ J) enter
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Fact A.25, p.62 (PDF 62)

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_PhiSobolev
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_phiDiv

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Fact A.25 (contraction of Φ-divergences).** Let `J` be an open interval and `Ψ` smooth on `J`
with `Ψ″ > 0`, `1/Ψ″` concave and `Ψ(1) = 0`. If `μ` satisfies the Ψ-Sobolev inequality (1) with
constant `C`, then for every `ν ≪ μ` and every `t > 0`,
`D_Ψ(νK_t ‖ μK_t) ≤ (Ct/(1 + Ct)) D_Ψ(ν ‖ μ)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Fact A.25, p.62 (PDF 62), citing [MW25a, Lemma 15].

**Formalization Note** `μ` and `ν` are probability measures on `ℝⁿ` and `dν/dμ` takes values in `J`
`μ`-a.e., as Definition 12 requires for `D_Ψ(ν ‖ μ)` (p.56). This forces `1 ∈ J`, since `dν/dμ` has
`μ`-mean `1`. `D_Ψ` is the `[0, ∞]`-valued `phiDiv`. No sign is imposed on `C`. -/
theorem fact_A_25 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] (J : Set ℝ)
    (hJ : IsOpenInterval J) (Ψ : ℝ → ℝ) (hΨ : AdmissiblePhi J Ψ) (hΨ1 : Ψ 1 = 0) (C : ℝ)
    (hC : PhiSobolev μ J Ψ C) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (hνμ : ν ≪ μ)
    (hνJ : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal ∈ J) (t : ℝ) (ht : 0 < t) :
    phiDiv Ψ (gamObs ν t) (gamObs μ t) ≤
      ENNReal.ofReal (C * t / (1 + C * t)) * phiDiv Ψ ν μ := by sorry

end PhiSobBayes
