-- Prove2me | Theorems.Thm_RandomOrderCRS_proposition_6
-- name    : RandomOrderCRS.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:59.968682+00:00
-- url     : https://prove2.me/theorems/c1f1470c-6a1e-4524-9d96-a150a7dc0209
-- title:
--   Proposition 6 — at most one simple-blocker; independence of $\mathrm{sbl}_f$
-- statement:
--   Fix an edge $e$ and $f\in\partial(e)$, with any attenuation function $a:[0,1]\to[0,1]$. Then:
--
--   1. $f$ has at most one simple-blocker;
--   2. the event $\mathrm{sbl}_f$ is independent from $S_f$ and $(Y_g,S_g)_{g\in\partial(e)\cup\{e\}\setminus\{f\}}$.
--
--   Item 1 turns the probability of $\mathrm{sbl}_f$ into a sum over candidates. Item 2 is what allows the bound of Lemma 3 to be multiplied with the probability of $\mathcal R_e=\{f\}$.
--
--   Differences from the source:
--   - encoding: $f$ has at most one simple-blocker → the claim for injective $Y$, i.e. almost surely; reason: two tied blockers are not relevant for each other, so the claim fails on that null set; the paper's sampling excludes it
--   - encoding: the event is independent from the random variables → `IndepFun` of the indicator of the event and the vector of those variables; reason: the same statement
--   - generalization: $x$ a fractional matching of $G$ (the setting of §1.1 and §3) → only $x_g\in[0,1]$ for every $g$, with no degree constraint; reason: both items concern only which coordinates the event reads, and the degree constraint is never used; every fractional matching satisfies the weaker hypothesis, so the statement specializes to the paper's
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Proposition 6, p.18

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_ArrivalModel
import Definitions.Def_RandomOrderCRS_SimpleBlocker

open ProbabilityTheory

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Proposition 6, MacRury, Ma & Grammel, arXiv:2209.07520v2, p.18. For any `f ∈ ∂(e)`:
1. `f` has at most one simple-blocker;
2. the event `sbl_f` is independent from `S_f` and `(Y_g, S_g)_{g∈∂(e)∪{e}\{f}}`.

**Formalization Note.** Item 1 is stated for injective `Y`, i.e. almost surely: if two blockers
tie, neither is relevant for the other, so it fails on that null set. Item 2 is the independence of
the indicator of `sbl_f` and the vector `(S_f, (Y_g, S_g)_g)`. The attenuation function is arbitrary,
as on p.17. -/
theorem proposition_6 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : ∀ e, x e ∈ Set.Icc (0 : ℝ) 1) (a : ℝ → ℝ)
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.Icc (0 : ℝ) 1) (e f : G.edgeSet)
    (hf : f ∈ edgeNbrs G e) :
    (∀ (Y : G.edgeSet → ℝ) (S : G.edgeSet → Bool), Function.Injective Y →
      ∀ h₁ h₂, IsSimpleBlocker G Y S e f h₁ → IsSimpleBlocker G Y S e f h₂ → h₁ = h₂) ∧
    IndepFun
      ({ω : Sample G | HasSimpleBlocker G ω.1 ω.2 e f}.indicator fun _ => (1 : ℝ))
      (fun ω : Sample G => (ω.2 f,
        fun g : {g // g ∈ (insert e (edgeNbrs G e)).erase f} => (ω.1 g, ω.2 g)))
      (arrivalMeasure G x a) := by sorry

end RandomOrderCRS
