-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_theorem_3_1
-- name    : PriceIgnorance.Pairwise.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:14:19.222431+00:00
-- url     : https://prove2.me/theorems/ef5ddfdc-e6a0-4ba5-aaf1-84a246b8c88b
-- title:
--   Theorem 3.1 — for every $k\ge2$, correlation-blind and correlation-aware optimal competitive ratios coincide (prophet and prophet secretary)
-- statement:
--   Fix $k\ge2$. For an arrival model let
--   $$\mathrm{blindCR}_k=\inf_{D_1,\dots,D_n}\ \sup_{A\in\mathrm{ALG}}\ \inf_{D\in kI}\ \frac{\mathbb E_{V\sim D}[\mathrm{val}(A,V)]}{\mathbb E_{V\sim D}[\max_iV_i]},\qquad \mathrm{awareCR}_k=\inf_{D_1,\dots,D_n}\ \inf_{D\in kI}\ \sup_{A\in\mathrm{ALG}}\ \frac{\mathbb E_{V\sim D}[\mathrm{val}(A,V)]}{\mathbb E_{V\sim D}[\max_iV_i]},$$
--   where the outer infima run over all $n$ and all non-degenerate marginals. Then
--   $$\mathrm{blindCR}_k=\mathrm{awareCR}_k$$
--   both for the prophet inequality (values in the fixed order $V_1,\dots,V_n$) and for the prophet secretary problem (values in a uniformly random order independent of the values).
--
--   So under $k$-wise independence, an algorithm that knows only the marginals loses nothing against the prophet compared with one that knows the joint law. Theorem 1.2 combines this with Theorems 3.16 and 3.19.
--
--   Differences from the source:
--   - encoding: inf over D_1..D_n with footnote 3 (0 < max_i E[V_i] < ∞, values ≥ 0) → inf over all n and NonDegenerate marginals (value laws, integrable, max mean > 0); reason: excludes only the cases where the ratios are undefined, as footnote 3 does
--   - encoding: sup/inf of ratios → real ⨆/⨅ over the algorithm class and over kI; reason: for non-degenerate marginals kI ∋ product law, denominators are positive and ratios lie in [0,1], so no junk value is reached
--   - encoding: randomized online algorithms (mixtures of deterministic ones) → behavioural stopping probabilities p_i(history) ∈ [0,1], measurable in the history; reason: same value functions as mixtures of deterministic rules (Kuhn); measurability makes E_D[val] defined
--   - encoding: uniformly random order independent of the values, val averaged over it (p. 7) → σ uniform on permutations of Fin n, independent of values and internal randomness; identities revealed; val averaged over σ; reason: the standard prophet secretary model the paper uses
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 5, Theorem 3.1 and the two displays after it (proof pp. 6–7)

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms
import Definitions.Def_PriceIgnorance_Pairwise_Ratios

namespace PriceIgnorance.Pairwise

/-- Theorem 3.1 (p. 5): for every `k ≥ 2` the optimal competitive ratio of correlation-blind
algorithms under `k`-wise independence equals that of correlation-aware algorithms, both for the
prophet inequality (fixed order) and for the prophet secretary problem (uniformly random order). -/
theorem theorem_3_1 (k : ℕ) (hk : 2 ≤ k) :
    blindCR fixedOrder k = awareCR fixedOrder k ∧
      blindCR randomOrder k = awareCR randomOrder k := by sorry

end PriceIgnorance.Pairwise
