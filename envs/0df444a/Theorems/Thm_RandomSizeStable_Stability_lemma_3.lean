-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_lemma_3
-- name    : RandomSizeStable.Stability.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:04.56188+00:00
-- url     : https://prove2.me/theorems/9db2e86a-6715-4870-a48c-c8e0cdc7bbd7
-- title:
--   Lemma 3 — excess-cost and fixed-cut threshold bounds (4.1)–(4.2)
-- statement:
--   Let $E$ be a finite nonempty strict-ranking profile, $P$ any lottery, and $d$ any consistent finite-valued pseudometric on the tagged voters and candidates. Fix a socially optimal candidate $o$. At threshold $t\ge0$ mark $H(t)=\{c:d(o,c)>t\}$, and compute $a_v(t),A_v(t)$ by the rank scan and positive-length marked blocks. Every voter $v$ and every fixed $q\in[0,1]$ satisfy
--   $$\sum_cP(c)d(v,c)-d(v,o)\le\int_0^\infty a_v(t)\,dt,$$
--   $$\int_0^\infty\mathbf1\{a_v(t)\le q<A_v(t)\}\,dt\le2d(v,o).$$
--   Both threshold functions are integrable. Stability is not assumed. The statement retains $d(v,o)=0$, arbitrary zero masses and the exact half-open cut condition.
--
--   These inequalities connect actual metric costs with the rank cutoffs used in Lemma 5.
--
--   Differences from the source:
--   - encoding: finite nonempty voter and candidate sets with strict rankings → finite nonempty types and Election strict total orders; reason: these represent exactly the finite profiles in Section 2, with uniform voter averaging
--   - encoding: a consistent metric, allowing distinct points at distance zero → a real-valued pseudometric on V ⊕ C with weak ranking consistency; reason: Section 2 footnote 3 explicitly allows zero distances between distinct points
--   - encoding: integrals from zero to infinity → Bochner integrals on (0,∞), with integrability asserted in the conclusion; reason: the endpoint has zero Lebesgue measure; the finite step functions vanish beyond the largest candidate distance, so no integrability hypothesis is added
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 12, Lemma 3, Equations (4.1) and (4.2).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankBlocks

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Lemma 3, p.12: both threshold bounds with the operational cutoffs.
Integrability is concluded, not added as a hypothesis. -/
theorem lemma_3 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (E : Election V C) (P : C → ℝ) (hP : P ∈ stdSimplex ℝ C)
    (d : V ⊕ C → V ⊕ C → ℝ) (hd : IsPseudometric d) (hc : Consistent E d)
    (o : C) (ho : ∀ c, candCost d o ≤ candCost d c) (v : V)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fun t => lowerCut E P v (marked d o t)) (Set.Ioi 0) ∧
    IntegrableOn (fun t : ℝ =>
      (if lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)
        then 1 else 0 : ℝ)) (Set.Ioi 0) ∧
    (∑ c, P c * d (Sum.inl v) (Sum.inr c)) - d (Sum.inl v) (Sum.inr o) ≤
      ∫ t in Set.Ioi (0 : ℝ), lowerCut E P v (marked d o t) ∧
    (∫ t in Set.Ioi (0 : ℝ),
      (if lowerCut E P v (marked d o t) ≤ q ∧ q < upperCut E P v (marked d o t)
        then 1 else 0 : ℝ)) ≤ 2 * d (Sum.inl v) (Sum.inr o) := by sorry

end RandomSizeStable.Stability
