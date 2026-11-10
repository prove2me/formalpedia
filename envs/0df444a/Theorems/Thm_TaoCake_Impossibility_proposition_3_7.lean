-- Prove2me | Theorems.Thm_TaoCake_Impossibility_proposition_3_7
-- name    : TaoCake.Impossibility.proposition_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:07:31.455374+00:00
-- url     : https://prove2.me/theorems/ebe49bfd-6a5a-40f8-b203-2f2a985ed4c4
-- title:
--   Proposition 3.7 — for small ε, M₁(F⁵) = X₁ and M₂(F⁵) = X₂
-- statement:
--   Throughout, the **cake** is $C = [0,1]$; a **value density** is a function $f$ that is **piecewise-constant** ($[0,1]$ is partitioned into finitely many intervals, $f$ constant on each) and **hungry** ($f(x) > 0$ for every $x \in [0,1]$). The utility of a set $X$ for density $f$ is $v_f(X) = \int_{X \cap [0,1]} f(x)\,dx$. A **mechanism** $M$ maps a reported profile $F = (f_1, f_2)$ to two disjoint measurable subsets $M_1(F), M_2(F)$ of $[0,1]$ (cake may be left unallocated). It is **proportional** if $v_{f_i}(M_i(F)) \ge \tfrac12 v_{f_i}([0,1])$ for every admissible $F$ and agent $i$, and **truthful** if $v_{f_i}(M_i(F)) \ge v_{f_i}(M_i(F[i \leftarrow g]))$ for every admissible $F$, agent $i$ and admissible misreport $g$.
--
--   Fix a truthful proportional mechanism $M$ (Section 3 argues by contradiction from one) and a real $\varepsilon$. The paper's instances are: $F^1 = (1, 1)$; $X_1 = M_1(F^1)$, $X_2 = M_2(F^1)$; $F^2 = (1, f^2_2)$ with $f^2_2 = \varepsilon$ on $X_1$ and $1$ on $X_2$; $F^3 = (f^3_1, f^2_2)$ with $f^3_1 = \tfrac12$ on $X_1$ and $1$ on $X_2$; $X_{11} = M_1(F^3) \cap X_1$, $X_{12} = M_2(F^3) \cap X_1$, $X_{21} = M_1(F^3) \cap X_2$, $X_{22} = M_2(F^3) \cap X_2$; $F^4 = (f^4_1, f^2_2)$ with $f^4_1 = 1, \varepsilon, 2\varepsilon, \varepsilon$ on $X_{11}, X_{12}, X_{21}, X_{22}$; $F^5 = (1, f^5_2)$ with $f^5_2 = 1-\varepsilon, \varepsilon, 1$ on $X_{11}, X_{12}, X_2$; and $F^6 = (f^4_1, f^5_2)$. Points outside the listed sets get density $\varepsilon$.
--
--   **Proposition 3.7** (p. 7). For every truthful, proportional mechanism $M$ there is $\varepsilon_0 > 0$ such that for every $\varepsilon$ with $0 < \varepsilon < \varepsilon_0$,
--
--   $$M_1(F^5) = X_1 \quad\text{and}\quad M_2(F^5) = X_2,$$
--
--   so Instance 5 receives the allocation of Instances 1 and 2. Instance 5 is the misreport target used in Proposition 3.9.
--
--   **Formalization Note** Agents are `Fin 2` (Lean agent `0` is the paper's agent 1). The hypotheses `IsFeasible M`, `IsTruthful M`, `IsProportional M` constrain `M` only at admissible profiles; the instances `profileK M ε` are not assumed admissible.
--
--   Differences from the source:
--   - generalization: allocation pieces are subsets of [0,1] whose utilities are the Riemann integrals ∫_X f_i(x) dx → pieces are arbitrary Lebesgue-measurable (NullMeasurableSet) pairwise disjoint subsets of [0,1]; utility is the Lebesgue integral of f over X ∩ [0,1]; reason: every set whose Riemann utility exists for a hungry piecewise-constant density is Lebesgue measurable with the same integral, so every source mechanism is covered; quantifying over more mechanisms specializes to the source
--   - encoding: agents 1 and 2 → agents 0 and 1 of Fin 2; reason: Lean indexing; Lean agent 0 is the paper's agent 1
--   - encoding: [0,1] can be partitioned into finitely many intervals with f constant on each → a family I : Fin n → Set ℝ of pairwise disjoint order-connected sets with union [0,1] and f constant on each I k; reason: order-connected subsets of ℝ are exactly the intervals (including degenerate and empty ones); same densities
--   - reading: Definitions 3.2 and 3.5 print X₁ = |M₁(F¹)|, X₂ = |M₂(F¹)| and X₁₁ = |M₁(F³) ∩ X₁| etc. (lengths) → X1 M = M₁(F¹), X2 M = M₂(F¹), X11 M ε = M₁(F³) ∩ X₁, X12 = M₂(F³) ∩ X₁, X21 = M₁(F³) ∩ X₂, X22 = M₂(F³) ∩ X₂ (sets); reason: obvious typo (insight I1): the text names these as the allocation and as four subsets, tests membership in them and takes their lengths afterwards
--   - reading: the densities of Instances 2–6 are specified only on the listed sets (X₁, X₂ or X₁₁, X₁₂, X₂₁, X₂₂) → a point in none of the listed sets gets the value ε, and the first listed case wins on an overlap; reason: the source leaves residue unspecified and treats the regions as a partition; for 0 < ε < 1 all branch values are positive, and the formulas agree on every listed region whenever those regions are disjoint; first-match priority also defines the function on raw extensions whose regions overlap, without asserting disjointness or coverage (I2–I3)
--   - reading: M is applied to the profiles F², …, F⁶ as if they were admissible reports (insight I3: they need not be piecewise-constant) → M is a raw function on all profiles, constrained only at admissible profiles; the claim must hold for every such M, with M(F^k) whatever M returns; reason: the source's M(F^k) is undefined when F^k is not admissible; no admissibility of F^k is assumed, since that would be an unproved extra hypothesis
--   - reading: 'let ε > 0 be a sufficiently small real number', fixed after the hypothetical mechanism M → ∃ ε₀ > 0 (allowed to depend on M) such that the claim holds for every ε with 0 < ε < ε₀; reason: the source's quantifier order: M is fixed first, then ε is taken small
-- source:
--   Biaoshuai Tao, On Existence of Truthful Fair Cake Cutting Mechanisms, arXiv:2104.07387v1, p. 7 (PDF 7), Proposition 3.7

import Mathlib
import Definitions.Def_TaoCake_Impossibility_Model
import Definitions.Def_TaoCake_Impossibility_Instances

open MeasureTheory

namespace TaoCake.Impossibility

/-- Proposition 3.7 (p. 7): for every sufficiently small `ε > 0`,
`M₁(F⁵) = X₁` and `M₂(F⁵) = X₂`. -/
theorem proposition_3_7
    (M : Mechanism) (hFeas : IsFeasible M) (hTruth : IsTruthful M) (hProp : IsProportional M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      M (profile5 M ε) 0 = X1 M ∧ M (profile5 M ε) 1 = X2 M := by sorry

end TaoCake.Impossibility
