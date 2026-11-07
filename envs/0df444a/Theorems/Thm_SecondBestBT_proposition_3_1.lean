-- Prove2me | Theorems.Thm_SecondBestBT_proposition_3_1
-- name    : SecondBestBT.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:00.487706+00:00
-- url     : https://prove2.me/theorems/c74e78e9-6df9-4abd-97e7-4acc12b2f74f
-- title:
--   Proposition 3.1 — allocation characterization for arbitrary priors
-- statement:
--   Let the seller's and buyer's values be drawn independently from arbitrary priors $F_S$ and $F_B$ supported on $[0,1]$, and let $x$ be a measurable allocation rule with $x(s,b)\in[0,1]$ for $s,b\in[0,1]$. Write $x_B$, $x_S$ for its interim allocations and $\Lambda_{\mathrm{gen}}$ for the generalized budget-balance discriminant. Then:
--
--   1. there are payment rules $p_B,p_S$ making $(x,p_B,p_S)$ a well-defined mechanism that is BIC and interim IR at every type in $[0,1]$ and ex-ante WBB **if and only if**
--   $$
--   x_B \text{ is weakly increasing on } [0,1],\qquad x_S \text{ is weakly decreasing on } [0,1],\qquad \Lambda^{F_S,F_B}_{\mathrm{gen}}(x)\ge0;
--   $$
--   2. the same characterization holds with pointwise SBB on $[0,1]^2$ in place of ex-ante WBB;
--   3. consequently, $\mathrm{SB}_{F_S,F_B}$ (types in $[0,1]$) is the supremum of $\mathrm{GFT}_{F_S,F_B}(x)$ over the measurable allocations with values in $[0,1]$ on $[0,1]^2$ satisfying the three conditions.
--
--   This extends the Myerson–Satterthwaite characterization to priors without densities, and shows that pointwise budget balance costs nothing relative to ex-ante weak budget balance.
--
--   Differences from the source:
--   - encoding: an allocation $x:[0,1]^2\to[0,1]$ → a Borel measurable $x:\mathbb R^2\to\mathbb R$ with values in $[0,1]$ on $[0,1]^2$; reason: the interim allocations and GFT are integrals of $x$; values off $[0,1]^2$ are not seen by priors on $[0,1]$
--   - encoding: mechanisms $(x,p_B,p_S)$ whose integrals are written without conditions → `WellDefined`: Borel measurable rules, $x\in[0,1]$ on $T\times T$, and finite interim-payment, budget-surplus and GFT integrals; reason: the paper's integrals presuppose these conditions; they only shrink the mechanism class, and the paper's constructions satisfy them
--   - encoding: independent priors $F_S,F_B$ supported on a set $A$ → probability measures on $\mathbb R$ with $\mu(\mathbb R\setminus A)=0$; independence is the product measure; reason: same objects
--   - encoding: $\mathrm{SB}$ as a supremum → `sSup` in $\mathbb R$; reason: the feasible GFT set is nonempty and bounded above by $\mathrm{FB}$ (proved in the verification file), so `sSup` is the supremum
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Proposition 3.1, p.6

import Mathlib
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_IsSBB
import Definitions.Def_SecondBestBT_secondBest
import Definitions.Def_SecondBestBT_lambdaGen

open MeasureTheory

namespace SecondBestBT

/-- **Proposition 3.1** (allocation characterization for arbitrary priors; Liu–Qin–Ren–Wang,
*Second-Best Bilateral Trade is 1/2 Efficient*, arXiv:2606.03849, held version sha256 17184930…,
Proposition 3.1, p.6). Let the priors `μS`, `μB` be arbitrary probability measures supported on
`[0, 1]`, and let `x` be a measurable allocation with values in `[0, 1]` on `[0, 1]²`.

1. `x` is implementable by a BIC, interim-IR, ex-ante WBB mechanism with types in `[0, 1]` iff
   `x_B` is weakly increasing on `[0, 1]`, `x_S` is weakly decreasing on `[0, 1]` and
   `Λ_gen(x) ≥ 0`.
2. The same characterization holds with pointwise SBB in place of ex-ante WBB.
3. Consequently `SB` is the supremum of `GFT(x)` over these allocations.

**Formalization Note** Implementability is the existence of payment rules `pB`, `pS` such that the
mechanism `(x, pB, pS)` is `WellDefined` (measurable, with the model's integrals finite) and
satisfies the constraints at every type of `[0, 1]`. The allocations in clause 3 are the
measurable `x` with values in `[0, 1]` on `[0, 1]²` satisfying the three conditions. -/
theorem proposition_3_1 (μS μB : Measure ℝ) (hS : IsPriorOn (Set.Icc 0 1) μS)
    (hB : IsPriorOn (Set.Icc 0 1) μB) :
    (∀ x : ℝ × ℝ → ℝ, Measurable x →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, x (s, b) ∈ Set.Icc (0 : ℝ) 1) →
      ((∃ pB pS : ℝ × ℝ → ℝ, IsFeasible (Set.Icc 0 1) μS μB ⟨x, pB, pS⟩) ↔
        (MonotoneOn (interimB μS x) (Set.Icc 0 1) ∧ AntitoneOn (interimS μB x) (Set.Icc 0 1) ∧
          0 ≤ lambdaGen μS μB x)) ∧
      ((∃ pB pS : ℝ × ℝ → ℝ, WellDefined (Set.Icc 0 1) μS μB ⟨x, pB, pS⟩ ∧
          IsBIC (Set.Icc 0 1) μS μB ⟨x, pB, pS⟩ ∧ IsInterimIR (Set.Icc 0 1) μS μB ⟨x, pB, pS⟩ ∧
          IsSBB (Set.Icc 0 1) ⟨x, pB, pS⟩) ↔
        (MonotoneOn (interimB μS x) (Set.Icc 0 1) ∧ AntitoneOn (interimS μB x) (Set.Icc 0 1) ∧
          0 ≤ lambdaGen μS μB x))) ∧
    secondBest (Set.Icc 0 1) μS μB =
      sSup (gft μS μB '' {x : ℝ × ℝ → ℝ | Measurable x ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, x (s, b) ∈ Set.Icc (0 : ℝ) 1) ∧
        MonotoneOn (interimB μS x) (Set.Icc 0 1) ∧ AntitoneOn (interimS μB x) (Set.Icc 0 1) ∧
        0 ≤ lambdaGen μS μB x}) := by sorry

end SecondBestBT
