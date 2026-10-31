-- Prove2me | Theorems.Thm_PandoraComb_proposition_4_3
-- name    : PandoraComb.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:36.217977+00:00
-- url     : https://prove2.me/theorems/d1598fbc-b413-4016-829f-e020d4ab7c43
-- title:
--   Proposition 4.3 — Transformation $T$ preserves the optimal utility, and impulsive strategies map back to fixed order strategies
-- statement:
--   Let $\mathcal I=(D_1,\dots,D_n,c)$ be an instance whose laws are supported in a grid $0=v_0<v_1<\dots<v_m$, with $c$ normalized and monotone, and let $\mathcal I'=T(\mathcal I)$ be the Bernoulli instance with boxes $(i,j)$, laws $D_{i,j}$ (value $v_j$ with probability $\mathbb P(V_i=v_j)/\mathbb P(V_i\le v_j)$) and cost $c'(S)=c(\{i\mid\exists j,(i,j)\in S\})$. Then:
--
--   1. for every admissible strategy $\pi$ on $\mathcal I$ there is an admissible strategy $\pi'$ on $\mathcal I'$ with $u(\mathcal I;\pi)\le u(\mathcal I';\pi')$;
--   2. for every admissible strategy $\pi'$ on $\mathcal I'$ there is an admissible strategy $\pi$ on $\mathcal I$ with $u(\mathcal I;\pi)\ge u(\mathcal I';\pi')$;
--   3. furthermore, for every impulsive strategy $\pi'$ on $\mathcal I'$ there is such a $\pi$ that is a fixed order strategy.
--
--   Together with Proposition 4.1 and Theorem 3.1 this yields Theorem 4.1.
--
--   Differences from the source:
--   - generalization: supp = {v_1, …, v_m}, exactly the union of the supports together with 0 → any grid 0 = v 0 < ⋯ < v m that carries every law; reason: an extra grid point gives copies with probability 0 (always zero boxes), and the proof's identity P(V_i ≤ v_k) = P(V_i < v_{k+1}) holds for any such grid; the paper's grid is an instance
--   - reading: "For every instance I" (p.20) → an instance whose laws are carried by a finite grid; reason: Transformation T (p.19) is defined only for "distributions with finite supports", so that is the domain of I′ = T(I)
--   - encoding: j ∈ [m], 0 = v_1 < ⋯ < v_m, boxes [n] × [m] (p.19) → j : Fin (m + 1), v 0 = 0, boxes ι × Fin (m + 1); reason: index shift only
--   - encoding: finite expectations and non-negativity of the D_i (p.7) → not stated separately; reason: both follow from support in the grid with v 0 = 0 < v 1 < ⋯
--   - encoding: "Furthermore, if π′ is impulsive, then there exists such a fixed-order strategy π" → a third clause for π′ = impulsive l with l without repetition, giving σ and π with IsFixedOrder σ π; reason: impulsive strategies on I′ are exactly these
--   - encoding: Π, all (randomized) strategies, deciding from the sequence of opened boxes and realized values so far, with coins tossed a priori (p.7) → admissible strategies: decisions read the ordered history and one uniform seed s ∈ [0,1] independent of the values, and are measurable in the observed values and the seed; reason: one uniform seed generates any finite family of coin tosses; measurability is what makes E[V(π)] and E[c(S(π))] defined, and it holds for every strategy the paper uses
--   - encoding: V(π) = max over S(π) of V_i, u(π) = E[V(π)] − E[c(S(π))] (p.7) → reward max(0, max observed value), utility = expectation of reward minus c(set of opened boxes); reason: values are non-negative a.s. and the empty strategy has utility 0 (pp.8, 24), so the two rewards agree a.s.
--   - encoding: boxes [n], c : 2^[n] → ℝ≥0 normalized and monotone (p.7) → boxes a finite type ι, c : Finset ι → ℝ with c ∅ = 0 and Monotone c; reason: relabeling [n] as ι changes no instance; c ≥ 0 follows from c ∅ = 0 and monotonicity
--   - encoding: a strategy chooses an uninspected box or halts (p.7) → a request for an already opened box halts the run; at most |ι| rounds; reason: a legal strategy never makes such a request, and |ι| rounds suffice to open every box
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, Proposition 4.3, p.20 (Transformation 2, p.19; proof p.20)

import Definitions.Def_PandoraComb_Model
import Definitions.Def_PandoraComb_FixedOrder
import Definitions.Def_PandoraComb_Bernoulli
import Definitions.Def_PandoraComb_Bernoullify

open MeasureTheory

namespace PandoraComb

/-- **Proposition 4.3** (arXiv:2303.01078v1, p.20): "For every instance I, let I′ = T(I). Then:
1. For every strategy π on instance I, there exists a strategy π′ on instance I′ such that
u(I;π) ≤ u(I′;π′).
2. For every strategy π′ on instance I′, there exists a strategy π on instance I such that
u(I;π) ≥ u(I′;π′). Furthermore, if π′ is impulsive, then there exists such a fixed-order
strategy π."

**Formalization Note.** Transformation `T` (p.19) is defined for instances with finitely
supported distributions: here every `D i` is a probability measure carried by a grid
`0 = v 0 < v 1 < ⋯ < v m` (`D i (range v)ᶜ = 0`), and the cost is normalized and monotone (§2,
p.7). `I′ = (bernoullify D v, liftCost c)` on the boxes `ι × Fin (m + 1)`. The impulsive
strategies of `I′` are the `impulsive l` for tuples `l` without repetition. -/
theorem proposition_4_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (D i)] (c : Finset ι → ℝ) (hc0 : c ∅ = 0) (hmono : Monotone c)
    {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : StrictMono v) (hv0 : v 0 = 0)
    (hsupp : ∀ i, D i (Set.range v)ᶜ = 0) :
    (∀ π : Strategy ι, Admissible π →
      ∃ π' : Strategy (ι × Fin (m + 1)), Admissible π' ∧
        utility D c π ≤ utility (bernoullify D v) (liftCost c) π') ∧
    (∀ π' : Strategy (ι × Fin (m + 1)), Admissible π' →
      ∃ π : Strategy ι, Admissible π ∧ utility (bernoullify D v) (liftCost c) π' ≤ utility D c π) ∧
    (∀ l : List (ι × Fin (m + 1)), l.Nodup →
      ∃ (σ : Fin (Fintype.card ι) ≃ ι) (π : Strategy ι), Admissible π ∧ IsFixedOrder σ π ∧
        utility (bernoullify D v) (liftCost c) (impulsive l) ≤ utility D c π) := by sorry

end PandoraComb
