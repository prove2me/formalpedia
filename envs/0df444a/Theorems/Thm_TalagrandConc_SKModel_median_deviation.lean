-- Prove2me | Theorems.Thm_TalagrandConc_SKModel_median_deviation
-- name    : TalagrandConc.SKModel.median_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:24.421974+00:00
-- url     : https://prove2.me/theorems/91a2ea94-c0ce-4be8-a52b-d55cfe52ad49
-- title:
--   Equation (12.5) — tails of log Z_N about a median (β-dependent form proved on p. 193)
-- statement:
--   Let $N\ge2$ and $\beta>0$. Let the couplings $(h_{ij})_{1\le i<j\le N}$ be i.i.d. with a common law $\nu$ on $\mathbb R$ satisfying the standing assumptions of Section 12: $\mathbb E h_{ij}=\mathbb E h_{ij}^3=0$, $\mathbb E h_{ij}^2=1$, $\mathbb E e^{\alpha|h_{ij}|}<\infty$ for some $\alpha>0$, together with the condition $\mathbb E e^{\pm h_{ij}}<2$ of Theorem 12.1. Write $F_N=\log Z_N$ for the logarithm of the partition function (12.1), and let $M_N$ be any median of $F_N$. Then for every $t$ with $0<t\le4\beta\sqrt N(N-1)$,
--
--   $$P(F_N\ge M_N+t)\le2\exp\Big(-\frac{t^2}{32\beta^2(N-1)}\Big)\qquad\text{and}\qquad P(F_N\le M_N-t)\le2\exp\Big(-\frac{t^2}{32\beta^2(N-1)}\Big).$$
--
--   This is the concentration of the free energy about its median, obtained from Corollary 2.4.4 applied on the $N(N-1)/2$ coordinates $h_{ij}$ with cost $\frac14|x-y|$ together with the Lipschitz bound (12.6). It is the first of the two steps in the proof of Theorem 12.1.
--
--   **Formalization Note** The printed display (12.5) on p. 192 reads $0<t\le4\sqrt N(N-1)\Rightarrow P(|\log Z_N-M_N|\ge t)\le2\exp(-t^2/(32(N-1)))$, without $\beta$. The derivation on p. 193 gives, for $u>v$ with $u-v\le4\beta\sqrt N(N-1)$, $P(\{\log Z_N>u\})P(\{\log Z_N<v\})\le\exp(-(u-v)^2/(32\beta^2(N-1)))$; taking $u$, $v$ near $M_N+t$, $M_N$ (resp. $M_N$, $M_N-t$) gives exactly the two one-sided bounds stated here. Each tail has the factor $2$; the two-sided event then has the factor $4$, which is why the statement is one-sided. For $\beta\le1$ the one-sided form of the printed range and exponent follows from this one by monotonicity in $t$. The hypothesis $N\ge2$ makes $N-1>0$. A median is a real $M$ with $P(F_N\le M)\ge\frac12$ and $P(F_N\ge M)\ge\frac12$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 192, Eq. (12.5); p. 193, the derivation of (12.5) from Corollary 2.4.4 and Eq. (12.6)

import Mathlib
import Definitions.Def_TalagrandConc_SKModel_Basic

namespace TalagrandConc.SKModel

/-- Talagrand (12.5), pp. 192–193, in the one-sided, β-dependent form that the proof on
p. 193 derives from Corollary 2.4.4: each tail of `log Z_N` about a median `M` is at most
`2 exp(-t² / (32 β² (N - 1)))` for `0 < t ≤ 4 β √N (N - 1)`. -/
theorem median_deviation (N : ℕ) (ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure ν] (β M t : ℝ)
    (hN : 2 ≤ N) (hβ : 0 < β) (hlaw : AdmissibleLaw ν)
    (htails : LightTails ν) (hM : IsMedian N ν β M)
    (ht : 0 < t) (htmax : t ≤ 4 * β * Real.sqrt N * (N - 1)) :
    (couplingLaw N ν {h | M + t ≤ freeEnergy N β h}).toReal ≤
        2 * Real.exp (-(t ^ 2) / (32 * β ^ 2 * (N - 1))) ∧
      (couplingLaw N ν {h | freeEnergy N β h ≤ M - t}).toReal ≤
        2 * Real.exp (-(t ^ 2) / (32 * β ^ 2 * (N - 1))) := by sorry

end TalagrandConc.SKModel
