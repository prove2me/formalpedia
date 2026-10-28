-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lemma_1
-- name    : ValuePersPricing.Deviation.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:22.756517+00:00
-- url     : https://prove2.me/theorems/d016ff07-33d9-40c0-aa43-84ff8206cd56
-- title:
--   Lemma 1, p. 9 — reduction to zero cost and unit mean: the ratio is unchanged and µc = 1, Sc = (S+M−1)/M, Mc = 1, Dc = D/M
-- statement:
--   Let $(F,c)$ be a market (a valuation $V\sim F$ with $V\ge c\ge 0$ almost surely and finite mean $\mu$) with $c<\mu$, i.e. margin $M=1-c/\mu>0$. Let $F_c$ be the law of the standardized valuation
--   $$V_c=\frac{V-c}{\mu-c}.$$
--   Then $(F_c,0)$ is a market with mean $\mu_c=1$, and
--   $$\mathcal R_{SP}(F,c)=(\mu-c)\,\mathcal R_{SP}(F_c,0),\qquad \mathcal R_{PP}(F,c)=(\mu-c)\,\mathcal R_{PP}(F_c,0),$$
--   so that $\mathcal R_{PP}(F,c)/\mathcal R_{SP}(F,c)=\mathcal R_{PP}(F_c,0)/\mathcal R_{SP}(F_c,0)$. Moreover $M_c=1$, $D_c=D/M$, if $F$ has scale $S$ then $F_c$ has scale $S_c=(S+M-1)/M$, and if $F$ has unbounded support so does $F_c$.
--
--   This reduction lets every bound be proved for $c=0$, $\mu=1$ and transported back to a general cost and mean.
--
--   **Formalization Note** $F_c$ is the pushforward `standardize ν c` of `ν` under $v\mapsto(v-c)/(\mu-c)$.
--
--   Differences from the source:
--   - generalization: the ratio identity R_PP(F,c)/R_SP(F,c) = R_PP(F_c,0)/R_SP(F_c,0) → the two scaling identities R_SP(F,c) = (µ−c)R_SP(F_c,0) and R_PP(F,c) = (µ−c)R_PP(F_c,0); reason: the proof on p. ec1 shows exactly these, and they imply the ratio identity whenever it is defined.
--   - generalization: the statistics of F_c → also that (F_c, 0) satisfies the standing assumptions and that unbounded support is preserved (S = ∞ gives S_c = ∞); reason: needed to apply the c = 0 results to F_c, including in the unbounded case; the extra conjuncts only add to the lemma.
--   - encoding: "let V_c := (V − c)/(µ − c)" → hypothesis c < µ; reason: V_c is undefined when µ = c, and µ ≥ c always holds.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. 9 (PDF 9), Lemma 1; proof p. ec1–ec2 (PDF 33–34)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Lemma 1 (p. 9): reduction to zero cost and unit mean. With `F_c` the law of
`V_c = (V − c)/(µ − c)`, the standardized market has cost `0` and mean `1`; both profits scale by
`µ − c` (so the ratio `R_PP/R_SP` is unchanged); `M_c = 1`, `D_c = D/M`,
`S_c = (S + M − 1)/M`, and unbounded support is preserved. -/
theorem lemma_1 (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hc : c < mean ν) :
    Market (standardize ν c) 0 ∧
    mean (standardize ν c) = 1 ∧
    spProfit ν c = (mean ν - c) * spProfit (standardize ν c) 0 ∧
    ppProfit ν c = (mean ν - c) * ppProfit (standardize ν c) 0 ∧
    margin (standardize ν c) 0 = 1 ∧
    coefDev (standardize ν c) = coefDev ν / margin ν c ∧
    (∀ S : ℝ, IsScale ν S → IsScale (standardize ν c) (sc (margin ν c) S)) ∧
    (Unbounded ν → Unbounded (standardize ν c)) := by sorry

end ValuePersPricing.Deviation
