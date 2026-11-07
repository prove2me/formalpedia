-- Prove2me | Theorems.Thm_SecondBestBT_appendix_A_truncation
-- name    : SecondBestBT.appendix_A_truncation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:19.540859+00:00
-- url     : https://prove2.me/theorems/ec10fec9-6d0d-4a5a-8053-8b1cdb639937
-- title:
--   Appendix A — truncation and scaling extend constant-factor guarantees to $[0,\infty)$
-- statement:
--   Let $F_S,F_B$ be independent priors on $[0,\infty)$ with $\mathrm{FB}<\infty$. For $V>0$ let $q_V=\Pr(s\le V)$, let the truncated instance condition the seller prior on $s\le V$ and cap the buyer's value at $\min\{b,V\}$, and let $\mathrm{FB}_V$, $\mathrm{SB}_V$ be its benchmarks, with types in $[0,V]$. Then:
--
--   1. if $q_V>0$, then $\mathrm{SB}\ge q_V\,\mathrm{SB}_V$, where $\mathrm{SB}$ has types in $[0,\infty)$;
--   2. if $q_V>0$, then $q_V\,\mathrm{FB}_V=\mathbb E\big[(\min\{b,V\}-s)^+\big]$;
--   3. $q_V\,\mathrm{FB}_V\to\mathrm{FB}$ as $V\to\infty$;
--   4. for every constant $c$: if $\mathrm{SB}_V\ge c\,\mathrm{FB}_V$ for all sufficiently large $V$, then $\mathrm{SB}\ge c\,\mathrm{FB}$;
--   5. for every $a>0$, every type set $T$ and all probability measures $F_S,F_B$, multiplying both agents' values and the type set by $a$ multiplies $\mathrm{SB}$ and $\mathrm{FB}$ by $a$:
--   $$
--   \mathrm{SB}_{aT}(aF_S,aF_B)=a\,\mathrm{SB}_T(F_S,F_B),\qquad \mathrm{FB}(aF_S,aF_B)=a\,\mathrm{FB}(F_S,F_B),
--   $$
--   so common scaling does not change the efficiency ratio.
--
--   These facts transfer a guarantee proved for priors on $[0,1]$ to all nonnegative priors with finite first-best GFT.
--
--   Differences from the source:
--   - reading: "for sufficiently large $V>0$, let $q_V>0$" → clauses 1 and 2 for every $V>0$ with $q_V>0$; reason: the size of $V$ is used only to make $q_V$ positive
--   - reading: "any bound $\mathrm{SB}_V\ge c\,\mathrm{FB}_V$ with a constant $c$ independent of $V$ passes to the original priors by letting $V\to\infty$" → the bound is assumed for all sufficiently large $V$; reason: letting $V\to\infty$ uses only large $V$; this is the weakest hypothesis of the sentence
--   - generalization: common scaling by $1/V$ normalizes $[0,V]$ to $[0,1]$ (and by $1/W$ for integer grids, p.7) → scaling by any $a>0$, for every type set $T$ and all probability measures; reason: specializes to $a=1/V$, $T=[0,V]$
--   - reading: the paper's BIC and IR for types in $[0,1]$, extended in Appendix A to all $s,b\ge0$ → BIC and IR at every type in $[0,\infty)$ for $\mathrm{SB}$, and in $[0,V]$ for $\mathrm{SB}_V$; reason: Appendix A extends mechanisms to all nonnegative types; quantifying only over the support would enlarge the class
--   - encoding: conditioning the seller prior on $s\le V$ and capping buyer values at $V$ → `ProbabilityTheory.cond μS (Set.Iic V)` and `μB.map (fun b => min b V)`; reason: same measures
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Appendix A, "Truncation and scaling", p.31

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_firstBest

open MeasureTheory Filter Topology

namespace SecondBestBT

/-- **Appendix A, "Truncation and scaling"** (Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2
Efficient*, arXiv:2606.03849, held version sha256 17184930…, Appendix A, p.31). Let `μS`, `μB`
be priors on `[0, ∞)` with `FB < ∞`. For `V > 0` let `q_V = Pr(s ≤ V)`, condition the seller prior
on `s ≤ V` and cap the buyer values at `V`; `FB_V`, `SB_V` are the benchmarks of this truncated
instance (types in `[0, V]`). Then:

1. if `q_V > 0`, `SB ≥ q_V · SB_V` (types in `[0, ∞)` for `SB`);
2. if `q_V > 0`, `q_V · FB_V = E[(min{b, V} − s)⁺]`, and `q_V · FB_V → FB` as `V → ∞`;
3. any bound `SB_V ≥ c · FB_V` holding for all sufficiently large `V`, with `c` independent of `V`,
   passes to the original priors: `SB ≥ c · FB`;
4. common scaling by `a > 0` of both values (and of the type set) multiplies `SB` and `FB` by
   `a`, so it does not change the efficiency ratio.

**Formalization Note** The conditioned seller prior is `ProbabilityTheory.cond μS (Set.Iic V)`, the
capped buyer prior is `μB.map (fun b => min b V)`. Clause 4 is stated for every type set `T` and
all probability measures; the paper uses it for `T = [0, V]` and `a = 1/V`. -/
theorem appendix_A_truncation (μS μB : Measure ℝ) (hS : IsPriorOn (Set.Ici 0) μS)
    (hB : IsPriorOn (Set.Ici 0) μB)
    (hFB : Integrable (fun p : ℝ × ℝ => max (p.2 - p.1) 0) (μS.prod μB)) :
    (∀ V : ℝ, 0 < V → 0 < μS.real (Set.Iic V) →
      μS.real (Set.Iic V) * secondBest (Set.Icc 0 V) (ProbabilityTheory.cond μS (Set.Iic V))
          (μB.map (fun b => min b V)) ≤ secondBest (Set.Ici 0) μS μB) ∧
    (∀ V : ℝ, 0 < V → 0 < μS.real (Set.Iic V) →
      μS.real (Set.Iic V) * firstBest (ProbabilityTheory.cond μS (Set.Iic V))
          (μB.map (fun b => min b V)) =
        ∫ p : ℝ × ℝ, max (min p.2 V - p.1) 0 ∂(μS.prod μB)) ∧
    Tendsto (fun V : ℝ => μS.real (Set.Iic V) *
        firstBest (ProbabilityTheory.cond μS (Set.Iic V)) (μB.map (fun b => min b V)))
      atTop (𝓝 (firstBest μS μB)) ∧
    (∀ c : ℝ, (∀ᶠ V : ℝ in atTop,
        c * firstBest (ProbabilityTheory.cond μS (Set.Iic V)) (μB.map (fun b => min b V)) ≤
          secondBest (Set.Icc 0 V) (ProbabilityTheory.cond μS (Set.Iic V))
            (μB.map (fun b => min b V))) →
      c * firstBest μS μB ≤ secondBest (Set.Ici 0) μS μB) ∧
    (∀ a : ℝ, 0 < a → ∀ (T : Set ℝ) (ν ρ : Measure ℝ), IsProbabilityMeasure ν →
      IsProbabilityMeasure ρ →
      secondBest ((fun v => a * v) '' T) (ν.map (fun v => a * v)) (ρ.map (fun v => a * v)) =
          a * secondBest T ν ρ ∧
        firstBest (ν.map (fun v => a * v)) (ρ.map (fun v => a * v)) = a * firstBest ν ρ) := by sorry

end SecondBestBT
