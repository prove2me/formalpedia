-- Prove2me | Theorems.Thm_RankOneBTF_proposition_11
-- name    : RankOneBTF.proposition_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:25:45.183593+00:00
-- url     : https://prove2.me/theorems/52250347-8468-4e14-afef-f6466b7bb211
-- title:
--   Proposition 11 — strict (50) and (51) make the ground truth the unique optimal solution of (fLP)
-- statement:
--   Under all assumptions of Proposition 10 (binary $\bar x,\bar y,\bar z$, $\mathcal F\ne\emptyset$, $0<\alpha<1$, Condition 1 of Proposition 7, Conditions 1–2 of Proposition 10), suppose moreover that inequalities (50) and all their symmetric counterparts hold **strictly**, and that inequalities (51) hold **strictly** for every $(i,j,k)\in\mathcal T\cap\mathcal P$. Then $(\bar x,\bar y,\bar z,\bar{\mathcal W})$ is the **unique** optimal solution of the flower LP (fLP) for $\mathcal G$; that is, (fLP) recovers the ground truth.
--
--   This is the deterministic recovery guarantee behind Theorem 4: the probabilistic part of the proof shows that each hypothesis holds with high probability.
--
--   Differences from the source:
--   - reading: "Let α < 1 be a constant arbitrarily close to 1" (inherited from Proposition 10) → for every α with 0 < α < 1; reason: as in Proposition 10
--   - encoding: all assumptions of Proposition 10, including (50) and (51) → the strict versions of (50) and (51) only; reason: the strict inequalities imply the non-strict ones; same instances
--   - encoding: fractions in (50), γ̄_ijk and (51) → real division with a/0 = 0; reason: under the hypotheses every denominator that occurs is positive
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §8.1, Proposition 11, p.29

import Mathlib
import Definitions.Def_RankOneBTF_flpRegion
import Definitions.Def_RankOneBTF_Prop7Cond1
import Definitions.Def_RankOneBTF_Prop10Cond1
import Definitions.Def_RankOneBTF_gammaBar

namespace RankOneBTF

/-- **Proposition 11** (arXiv:2202.07053v3, §8.1, p.29): "Suppose that all assumptions of
Proposition 10 hold; moreover, suppose that inequalities (50) (and symmetric counterparts) and
inequalities (51) are strictly satisfied. Then (x̄, ȳ, z̄, W̄) is the unique optimal solution of
Problem (fLP)."

**Formalization Note** The assumptions of Proposition 10 are `ℱ ≠ ∅`, `0 < α < 1`, Condition 1
of Proposition 7 and Conditions 1–4 of Proposition 10; Conditions 3 and 4 are implied by their
strict versions `Ineq50Strict` and `Ineq51Strict α`, which are assumed instead. The conclusion
is `FLPRecovers G x̄ ȳ z̄`: the ground truth is the unique optimal solution of (fLP) for `G`. -/
theorem proposition_11 {n m l : ℕ} (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool)
    (G : BTensor n m l) (hF : ∃ i j k, G i j k ≠ groundTruth xb yb zb i j k)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h7 : Prop7Cond1 xb yb zb G) (h1 : Prop10Cond1 xb yb zb G) (h2 : Prop10Cond2 α xb yb zb G)
    (h3 : Ineq50Strict xb yb zb G) (h4 : Ineq51Strict α xb yb zb G) :
    FLPRecovers G xb yb zb := by sorry

end RankOneBTF
