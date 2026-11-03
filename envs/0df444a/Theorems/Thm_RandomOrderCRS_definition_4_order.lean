-- Prove2me | Theorems.Thm_RandomOrderCRS_definition_4_order
-- name    : RandomOrderCRS.definition_4_order
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:01.446455+00:00
-- url     : https://prove2.me/theorems/f932d899-50df-4800-a1f0-4778f22f6b1d
-- title:
--   Definition 4 and Remark 3 — arrival times induce the uniform order
-- statement:
--   Let each edge $e$ have an independent uniform arrival time $Y_e\in[0,1]$, and sort the edges by arrival time. Then:
--
--   1. almost surely all arrival times are distinct;
--   2. for every real function $h$ of the order, $\mathbb E[h(\text{sorted order})]=\frac1{|E|!}\sum_\sigma h(\sigma)$;
--   3. for Algorithm 2 with attenuation function $a:[0,1]\to[0,1]$, the selection probability of $e$ averaged over all orders equals $\mathbb P[e\in\mathcal M]$ in the arrival-time model with independent $S_e\sim\mathrm{Ber}(s(x_e))$.
--
--   Remark 3 calls this reformulation a standard technique. It connects the definition of selectability with the analysis of §3, which works entirely with arrival times.
--
--   Differences from the source:
--   - encoding: edges arrive in increasing order of arrival times → `arrivalOrder`, a stable sort with a fixed tie-break; reason: ties have probability 0 (clause 1)
--   - encoding: $S_e:=X_e\cdot A_e$ with $X_e$ and $A_e$ from the algorithm → clause 3 identifies Algorithm 2 with the model $S_e\sim\mathrm{Ber}(s(x_e))$; reason: the paper's statement that each edge survives independently with probability $s(x_e)$, p.17
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Definition 4, p.16; Remark 3, pp.16–17

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Policy
import Definitions.Def_RandomOrderCRS_Attenuation
import Definitions.Def_RandomOrderCRS_AttenuateROM
import Definitions.Def_RandomOrderCRS_ArrivalModel

open MeasureTheory

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The arrival-time reformulation, MacRury, Ma & Grammel, arXiv:2209.07520v2, Definition 4 and
Remark 3, pp.16–17: "we will treat each edge e as having an arrival time Y_e drawn independently and
uniformly from [0, 1]. Edges then arrive in increasing order of arrival times."
1. Ties have probability 0.
2. The order sorted by `Y` is uniform on the `|E|!` orders.
3. For Algorithm 2, the selection probability averaged over the orders equals `ℙ[e ∈ ℳ]` in the
   arrival-time model with `S_e ∼ Ber(s(x_e))`. -/
theorem definition_4_order (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsFractionalMatching G x) (a : ℝ → ℝ)
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ᵐ Y ∂arrivalTimeLaw G, Function.Injective Y) ∧
    (∀ h : ArrivalOrder G → ℝ,
      ∫ Y, h (arrivalOrder G Y) ∂arrivalTimeLaw G =
        ((Fintype.card G.edgeSet).factorial : ℝ)⁻¹ * ∑ σ : ArrivalOrder G, h σ) ∧
    ∀ e : G.edgeSet,
      ((Fintype.card G.edgeSet).factorial : ℝ)⁻¹ *
          ∑ σ : ArrivalOrder G, selProb G (attenuateROM G x a hx ha) x σ e =
        arrivalProb G x a fun Y S => e ∈ greedy G (arrivalOrder G Y) S := by sorry

end RandomOrderCRS
