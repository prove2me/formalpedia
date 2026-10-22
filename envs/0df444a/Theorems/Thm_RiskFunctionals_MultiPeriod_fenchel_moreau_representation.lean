-- Prove2me | Theorems.Thm_RiskFunctionals_MultiPeriod_fenchel_moreau_representation
-- name    : RiskFunctionals.MultiPeriod.fenchel_moreau_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:06.192649+00:00
-- url     : https://prove2.me/theorems/2a40d1af-bc1a-4ad4-8c44-f9ac8519311e
-- title:
--   Eq. (3.20) — Fenchel–Moreau representation of a proper concave u.s.c. multi-period functional
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $\boldsymbol{\mathcal F}=(\mathcal F_t)_{t=0}^T$ a filtration with $\mathcal F_0=\{\emptyset,\Omega\}$, $p\in[1,\infty)$ and $1/p+1/q=1$. Let $\mathcal Y=\times_{t=1}^TL_p(\mathcal F_t)$ and $\mathcal Z=\times_{t=1}^TL_q(\mathcal F_t)$, with the pairing $\langle Z,Y\rangle=\sum_{t=1}^T\mathbb E(Y_tZ_t)$. Let $\mathcal A:\mathcal Y\to\overline{\mathbb R}$ be proper, concave and upper semicontinuous, and let $\mathcal A^+$ be its conjugate (3.19). Then, for every $Y\in\mathcal Y$,
--   $$\mathcal A(Y)=\inf\{\langle Z,Y\rangle-\mathcal A^+(Z):Z\in\mathcal Z\}.\tag{3.20}$$
--
--   This is the Fenchel–Moreau–Rockafellar theorem on the product space $\mathcal Y$, in the concave form. It is the starting point of the multi-period representations (3.21)–(3.23).
--
--   **Formalization Note** Proper means $\mathcal A<+\infty$ everywhere and $\mathcal A>-\infty$ somewhere. Concavity is computed in `EReal`, and upper semicontinuity is with respect to the product topology on $\mathcal Y$, which is the norm topology of $\|Y\|_p=(\sum_t\mathbb E|Y_t|^p)^{1/p}$. The infimum is in `EReal` over all of $\mathcal Z$. The trivial $\mathcal F_0$ is the standing assumption of §3.2.1.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 136, Eq. (3.20)

import Mathlib
import Definitions.Def_RiskFunctionals_MultiPeriod_Functionals

namespace RiskFunctionals.MultiPeriod

open MeasureTheory

/-- Eq. (3.20) (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007,
p. 136), on `𝒴 = ×_{t=1}^T L_p(ℱ_t)`, `𝒵 = ×_{t=1}^T L_q(ℱ_t)`, `1 ≤ p < ∞`,
`1/p + 1/q = 1`, for a filtration with trivial `ℱ₀`: the representation
`𝒜(Y) = inf{⟨Z, Y⟩ − 𝒜⁺(Z) : Z ∈ 𝒵}` holds if `𝒜` is proper, concave and upper
semicontinuous, with `𝒜⁺` the conjugate (3.19). -/
theorem fenchel_moreau_representation {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (𝔽 : Filtration (Fin (T + 1)) m0) (h𝔽 : 𝔽 0 = ⊥)
    (A : ProcessSpace P T p 𝔽 → EReal) (hproper : IsProper A) (hconc : IsConcaveFunctional A)
    (husc : UpperSemicontinuous A) :
    ∀ Y : ProcessSpace P T p 𝔽,
      A Y = ⨅ Z : ProcessSpace P T q 𝔽, ((pairing Z Y : ℝ) : EReal) - concaveConj q A Z := by sorry

end RiskFunctionals.MultiPeriod
