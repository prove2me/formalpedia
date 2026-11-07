-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_7_3_first_selection
-- name    : ShortBroadcastDom.lemma_7_3_first_selection
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:37.756913+00:00
-- url     : https://prove2.me/theorems/c0a223c0-dfd5-4793-a8e4-d716a77d6132
-- title:
--   Lemma 7.3 — first selection: $B\subseteq R_0$, costs in $[1,b]$, and the budget transfer $|F|+C^*\le b\gamma_f(G)$
-- statement:
--   Let $d=2a$ be an integer with $a\ge1$, $b=d+1$, and let $B$, $F$, $R_0$ and the costs $c(v)=b-|N_G(v)\cap F|$ ($v\notin F$) be the first selection of §7.2. Let $C^*$ be the minimum cost of a fractional cover of $R_0$ by candidates outside $F$ with costs $c$. Then
--
--   1. $B\subseteq R_0$;
--   2. for every candidate $v\notin F$: $c(v)$ is an integer with $1\le c(v)\le b$; $c(v)=b$ exactly when $v\in R_0$; and if $c(v)<b$ then $|N_G[v]\cap R_0|\le c(v)-1$;
--   3. $|F|+C^*\le b\,\gamma_f(G)$.
--
--   Part 3 is the budget transfer: after selecting $F$, the remaining fractional optimum fits in the budget $b\gamma_f(G)$.
--
--   Differences from the source:
--   - encoding: C∗, the fractional optimum of the remaining problem on G − F → tauOn G (V \ F) R₀ c in G (covers supported on V \ F); reason: no demand has a neighbour in F, so the constraints are the same in G and in G − F
--   - encoding: d = 2a an integer, a ≥ 1 → d : ℕ with 2 ≤ d; reason: the same parameters
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.2, p.46 (PDF p.49), Lemma 7.3

import Mathlib
import Definitions.Def_ShortBroadcastDom_firstSel
import Definitions.Def_ShortBroadcastDom_tauOn

namespace ShortBroadcastDom

/-- **Lemma 7.3 (first selection and budget transfer).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §7.2, p.46 (PDF 49): "(i) B ⊆ R0.
(ii) The costs are integers with 1 ≤ c(v) ≤ b, and c(v) = b holds exactly when v ∈ R0. If c(v) < b,
then |NG[v] ∩ R0| ≤ c(v) − 1. (iii) |F| + C∗ ≤ bγf(G)."

Setting (p.45): `d = 2a` is an integer (`a ≥ 1`, so `d ≥ 2`), `b = d + 1`, `B` the defects,
`F = V(G) \ N_G[B]`, `R₀ = V(G) \ N_G[F]`, `c(v) = b − |N_G(v) ∩ F|` for candidates `v ∉ F`, and
`C∗` the fractional optimum of covering `R₀` by candidates outside `F` with costs `c`.

**Formalization Note** `C∗ = tauOn G (V \ F) R₀ c` (fractional covers supported on `V \ F`, in
`G`; a demand has no neighbour in `F`, so this is the problem on `G − F`). Part (ii) is stated for
every candidate `v ∉ F`. -/
theorem lemma_7_3_first_selection {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) :
    defects G d ⊆ remDemands G d ∧
    (∀ v, v ∉ firstSel G d →
      (∃ z : ℤ, selCost G d v = z) ∧ 1 ≤ selCost G d v ∧ selCost G d v ≤ (d : ℝ) + 1 ∧
      (selCost G d v = (d : ℝ) + 1 ↔ v ∈ remDemands G d) ∧
      (selCost G d v < (d : ℝ) + 1 →
        ((closedNbhd G v ∩ remDemands G d).card : ℝ) ≤ selCost G d v - 1)) ∧
    ((firstSel G d).card : ℝ) +
        tauOn G (Finset.univ \ firstSel G d) (remDemands G d) (selCost G d) ≤
      ((d : ℝ) + 1) * fracDom G := by sorry

end ShortBroadcastDom
