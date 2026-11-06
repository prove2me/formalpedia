-- Prove2me | Theorems.Thm_UnobservedWelfare_lemma_2_4
-- name    : UnobservedWelfare.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:37.226754+00:00
-- url     : https://prove2.me/theorems/289a4e93-8933-4ec5-8357-e429553b639b
-- title:
--   Lemma 2.4 — a comparison price $p^\star$ exists
-- statement:
--   For an admissible cost $c$ and a centered i.i.d. buyer model satisfying RC at scale $W$, there is a deterministic price $p^\star\gg0$ with
--   $$B(p^\star)\le\inf_{p\gg0}B(p)+\varepsilon_T\quad\text{and}\quad c^*(p^\star)\le W,\tag{34}$$
--   where $B(p)=\mathbb E_\theta[S_\theta(p)]+c^*(p)$ and $\varepsilon_T=W/(T+1)$.
--
--   The infimum of $B$ need not be attained; $p^\star$ is the price against which every later comparison is made.
--
--   Differences from the source:
--   - encoding: $B(p^\star)\le\inf_{p\gg0}B(p)+\varepsilon_T$ → $B(p^\star)\le B(p)+\varepsilon_T$ for every $p\gg0$; reason: the two conditions are equivalent and the second needs no real infimum
--   - encoding: the standing normalization "we work with the centered utilities ... so $S_\theta(1)=0$" (p.18) → the hypothesis $\forall\theta,\ S_\theta(1)=0$; reason: the paper normalization made explicit; centering preserves demand, records, RC and $\mathrm{OPT}-\mathrm{ALG}$
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), Lemma 2.4 (34), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret
import Definitions.Def_UnobservedWelfare_roundLoss

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- **Lemma 2.4 (comparison price)** (Cheng–Tao–Xing, *Maximizing Unobserved Welfare: Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), Lemma 2.4 (34), p.19 (PDF p.21)). For a centered
(`S_θ(1) = 0`) i.i.d. buyer model satisfying RC at scale `W` and an admissible cost, there exists a
deterministic price `p⋆ ≫ 0` with `B(p⋆) ≤ inf_{p≫0} B(p) + ε_T` and `c*(p⋆) ≤ W`.

**Formalization Note** `IsComparisonPrice` writes `B(p⋆) ≤ inf_{p≫0} B(p) + ε_T` as
`∀ p ≫ 0, B(p⋆) ≤ B(p) + ε_T`. The centering is the paper's standing normalization of the RC
analysis (p.18). -/
theorem lemma_2_4 {m : ℕ} (hm : 1 ≤ m) (T : ℕ) (hT : 1 ≤ T) (W : ℝ) (hW : 0 < W)
    (c : (Fin m → ℝ) → ℝ) (hc : IsAdmissibleCost c)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (u : Θ → (Fin m → ℝ) → EReal) (hu : IsBuyerModel u) (hRC : ∀ θ, IsRC W (u θ))
    (hcen : ∀ θ, surplus (u θ) 1 = 0) :
    ∃ pstar : Fin m → ℝ, IsComparisonPrice u P c W T pstar := by sorry

end UnobservedWelfare
