-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_2_2
-- name    : PottsRapidMixing.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:54.847148+00:00
-- url     : https://prove2.me/theorems/d01e324a-bcde-405a-a6a0-7e4105f0aff9
-- title:
--   Lemma 2.2, p.10 — $\mathrm{gap}(M)$ against the FK gap
-- statement:
--   Let $G=(V,E)$ be a finite graph with an edge, $q\ge2$, $\beta>0$, $r\in(0,1)$, and let $M=M(r)$ be the chain of Definition 1.8. Then
--   $$\mathrm{gap}(M)\ge\frac{r}{2\Bigl(\frac{1}{\mathrm{gap}(P_{\mathrm{FK}})\,|E|}+1\Bigr)},$$
--   where $\mathrm{gap}$ is the variational gap $\inf_{f:\mathrm{Var}_\mu(f)\ne0}\mathcal E_P(f,f)/\mathrm{Var}_\mu(f)$ of p.10, and $P_{\mathrm{FK}}$ is FK dynamics at $p=1-e^{-\beta}$.
--
--   The lemma reduces the gap of the global chain $M$ to the gap of a single-edge chain, at the cost of a factor $r/2$.
--
--   **Formalization Note** $\mathrm{gap}$ is the published `LogSobolevMC.ChiSquare.gap`, an infimum over a nonempty set here because $q\ge2$ and $G$ has an edge.
--
--   Differences from the source:
--   - generalization: M = M(r) for r = (B − 1)/(B̃ − 1) with (2.1) → every r ∈ (0, 1), with B̃ = 1 + (B − 1)/r; reason: Lemma 4.1 and p.26 hold for arbitrary r ∈ (0, 1); the r of (2.1) lies there when β < β_u
--   - encoding: G with edge set E, in the expression 1/(gap(P_FK)·|E|) → hypothesis that G has an edge; reason: a nondegeneracy condition: without an edge the expression is undefined
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 2.2, p.10; Lemma 4.1, p.26

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting
import Definitions.Def_mm_mcmc
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 2.2** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.10). For `M = M(r)`,
`gap(M) ≥ r / (2 (1/(gap(P_FK) |E|) + 1))`, where `gap` is the variational gap of p.10.

**Formalization Note.** The statement holds for every `r ∈ (0, 1)` (Lemma 4.1 and p.26: `B̃ = 1 + (B − 1)/r`
with `r` arbitrary), which covers `r = (B − 1)/(B̃ − 1)` of (2.1). `G` is any finite graph with an edge, so
both gaps are infima over nonempty sets. -/
theorem lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hE : G.edgeSet.Nonempty) :
    r / (2 * (1 / (LogSobolevMC.ChiSquare.gap (fkChain G (pOf β) (q : ℝ)) (rcLaw G (pOf β) (q : ℝ)) *
        (Fintype.card G.edgeSet : ℝ)) + 1))
      ≤ LogSobolevMC.ChiSquare.gap (chainM G β q r) (pottsLaw G β q) := by sorry

end PottsRapidMixing
