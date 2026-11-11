-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_theorem_1_2
-- name    : PriceIgnorance.Pairwise.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:14:28.330204+00:00
-- url     : https://prove2.me/theorems/d5273149-b4e8-4b26-b84b-367b679da372
-- title:
--   Theorem 1.2 — for pairwise-independent prophet inequalities and prophet secretary, the price of ignorance equals the optimal competitive ratio
-- statement:
--   Let $\mathrm{ALG}$ be the randomized online stopping algorithms. Given marginals $D_1,\dots,D_n$ of nonnegative values with $0<\max_i\mathbb E[V_i]<\infty$, let $PI(D_1,\dots,D_n)$ be the pairwise-independent joint laws with these marginals. The **price of ignorance** (Definition 2.2) is
--   $$\mathrm{PoI}=\inf_{n,\,D_1,\dots,D_n}\ \sup_{B\in\mathrm{ALG}}\ \inf_{D\in PI}\ \inf_{A\in\mathrm{ALG}}\ \frac{\mathbb E_D[\mathrm{val}(B,V)]}{\mathbb E_D[\mathrm{val}(A,V)]}.$$
--   It is the worst-case ratio between the best correlation-blind algorithm, which knows only the marginals, and the best correlation-aware online algorithm, which knows $D$. The optimal (correlation-aware) **competitive ratio** is
--   $$\mathrm{CR}=\inf_{n,\,D_1,\dots,D_n}\ \inf_{D\in PI}\ \sup_{A\in\mathrm{ALG}}\ \frac{\mathbb E_D[\mathrm{val}(A,V)]}{\mathbb E_D[\max_iV_i]}.$$
--   Then
--   $$\mathrm{PoI}=\mathrm{CR}$$
--   both for the prophet inequality (values arrive in the fixed order $V_1,\dots,V_n$) and for the prophet secretary problem (values arrive in a uniformly random order independent of the values, identities revealed, and $\mathrm{val}$ averaged over the order).
--
--   The inequality $\mathrm{PoI}\ge\mathrm{CR}$ is the easy direction. The content is that a correlation-blind algorithm cannot approximate the optimal correlation-aware *online* algorithm better than the prophet can be approximated online.
--
--   Differences from the source:
--   - encoding: inf_A E_D[val(B,V)] / E_D[val(A,V)] (Definition 2.2) → E_D[val(B,V)] / sup_A E_D[val(A,V)]; reason: same value: the numerator is ≥ 0 and the sup is ≥ max_i E[V_i] > 0
--   - encoding: inf over D_1..D_n with footnote 3 (0 < max_i E[V_i] < ∞, values ≥ 0) → inf over all n and NonDegenerate marginals (value laws, integrable, max mean > 0); reason: excludes only the cases where the ratios are undefined, as footnote 3 does
--   - encoding: sup/inf of ratios → real ⨆/⨅ over the algorithm class and over kI; reason: for non-degenerate marginals kI ∋ product law, denominators are positive and ratios lie in [0,1], so no junk value is reached
--   - encoding: randomized online algorithms (mixtures of deterministic ones) → behavioural stopping probabilities p_i(history) ∈ [0,1], measurable in the history; reason: same value functions as mixtures of deterministic rules (Kuhn); measurability makes E_D[val] defined
--   - encoding: uniformly random order independent of the values, val averaged over it (p. 7) → σ uniform on permutations of Fin n, independent of values and internal randomness; identities revealed; val averaged over σ; reason: the standard prophet secretary model the paper uses
--   - encoding: the competitive ratio → awareCR with k = 2 (inf over marginals and D ∈ PI of sup_A E_D[val]/E_D[max]); reason: the optimal correlation-aware competitive ratio of p. 1 and Theorem 3.1's second display; by Theorem 3.1 it equals the blind one
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 2, Theorem 1.2 (special case of Theorems 3.16 & 3.19, with Theorem 3.1); p. 3, Definition 2.2; p. 1

import Mathlib
import Definitions.Def_PriceIgnorance_Pairwise_Algorithms
import Definitions.Def_PriceIgnorance_Pairwise_Ratios

namespace PriceIgnorance.Pairwise

/-- Theorem 1.2 (p. 2): for the pairwise-independent prophet inequality and for the
pairwise-independent prophet secretary problem, the price of ignorance equals the optimal
(correlation-aware) competitive ratio. -/
theorem theorem_1_2 :
    PoI fixedOrder 2 = awareCR fixedOrder 2 ∧ PoI randomOrder 2 = awareCR randomOrder 2 := by sorry

end PriceIgnorance.Pairwise
