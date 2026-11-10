-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_claim_4_11
-- name    : VecKnapsackMitM.Main.claim_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:35:12.821738+00:00
-- url     : https://prove2.me/theorems/a4f8ab0d-c102-4989-b657-09e2e943ece9
-- title:
--   Claim 4.11 — the convolution of an $\alpha$- and a $\beta$-approximate function is $(\max\{\alpha,\beta\}+1)$-approximate; computable in $(\log(n/\eta)/\varepsilon)^{O(d)}$
-- statement:
--   Setting of the proof of Lemma 4.8: $d\ge2$, $n=2^k\ge2$, nonnegative items, middle weight estimates $\bar W_2,\dots,\bar W_{d-1}\ge0$, $\varepsilon,\eta\in(0,1]$, $\delta=\varepsilon/(10\log n)$, $\Delta=(\varepsilon\eta/(10n))^5$.
--
--   (1) For real $\alpha,\beta\ge0$, let $A,B\subseteq I$ be nonempty and disjoint, $f$ $\alpha$-approximate on $A$ and $g$ $\beta$-approximate on $B$. If $\gamma:=\max\{\alpha,\beta\}+1\le\log n$, then every convolution $h=f\oplus g$ (any tie-breaking) is $\gamma$-approximate on $C:=A\cup B$.
--
--   (2) Moreover, there are one admissible real-RAM program and one absolute constant $C$ such that, in this setting, for all nonempty disjoint $A,B$, every $A$-function $f$ and $B$-function $g$ given as explicit tables (layout `ConvInput`, which also supplies $\max_Ap$, $\max_A\bar w_1$, $\max_Bp$, $\max_B\bar w_1$), the program halts within $C\cdot(\log_2(n/\eta)/\varepsilon)^{C\cdot d}$ steps with the table of some convolution $f\oplus g$ on $R^{A\cup B}$ at the address in $N[5]$.
--
--   Differences from the source:
--   - encoding: the setting of the proof of Lemma 4.8: n ≥ 2 a power of two, δ := ε/(10 log n), ∆ := (εη/(10n))^5, fixed W̄_2, …, W̄_{d−1}, ε, η ∈ (0, 1] → hypotheses n = 2^k with 1 ≤ k, nonnegative items and middle estimates, ε, η ∈ (0, 1]; δ and ∆ are the definitions cDelta, cBigDelta; log n = k; reason: the claims are stated inside that proof, which fixes these objects; nothing is added
--   - encoding: vectors x ∈ ℝ^d_{≥0} with x_0 the profit and x_1, …, x_{d−1} weights; R^J ⊆ ℝ^d → PVec d with prof = x_0 and wt t = x_{t+1} for t + 1 < d; the unused coordinate wt (d − 1) is 0 on R^J (InDom); reason: zero-based weight indices; R^J is the same finite set
--   - encoding: an A-function maps x ∈ R^A to ⊥ or a virtual item with set ⊆ A; p(⊥) = ∞, w̄(⊥) = −∞ → AFun d n := PVec d → Option (Finset (Fin n)), none for ⊥ and the represented set otherwise; properties 1–3 of Definition 4.10 are required only when the value is not ⊥; reason: a virtual item is used only through p, w̄ and set, which are those of its set; at ⊥ properties 1–3 hold by the ∞ conventions, so requiring them only off ⊥ is the same definition
--   - encoding: Definition 4.10 for real γ ≥ 0 → γ : ℝ with 0 ≤ γ in IsApproxOn; real powers in QSet; dyadic depths are cast to ℝ; reason: retains all nonnegative real approximation levels of Definition 4.10 and Claim 4.11, including noninteger levels
--   - encoding: "compute functions" (explicit tables, proof of Claim 4.13) → tables in memory (TableRep: a list of entries whose keys are exactly the points of R^J, each with ⊥ or a virtual item record); reason: the paper stores the functions explicitly; a table is the machine form of that
--   - reading: "given f, g, the function h can be computed" → the tables of f and g, the parameters d, n, ε, η, the estimates, and the scale data max_A p, max_A w̄_1, max_B p, max_B w̄_1 are in memory (ConvInput), every input table and record in the address window [6 + d, F) with F = N[4] the first free address; the output table address is N[5]; reason: these numbers fix the domains R^A, R^B, R^{A∪B} on which f, g and h are defined, so they are part of what "given f, g" means; with a polylogarithmic budget A and B cannot be read item by item
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - reading: "in time X" (no explicit O) → at most C·X executed instructions, with the same absolute C as in the exponent; reason: ordinary asymptotic running-time notation permits an absolute leading constant; this does not resolve the separate dimension-uniform base-one issue in INSIGHTS I3, whose printed formulas are retained
--   - generalization: the time assertion follows the hypotheses that f and g are approximate → the time assertion computes the convolution of arbitrary A- and B-functions; reason: the triple-enumeration computation uses only the tables and virtual-item summaries; approximate functions are a subclass
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Claim 4.11, printed p. 25 (PDF 26); Definitions 4.9–4.10, printed pp. 24–25 (PDF 25–26)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_Convolution

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Claim 4.11, printed p. 25 (PDF 26), in the setting of
the proof of Lemma 4.8 (`n = 2^k ≥ 2`, `δ = ε/(10 log n)`, `∆ = (εη/(10n))^5`, estimates
`W̄_2, …, W̄_{d−1} ≥ 0`, `ε, η ∈ (0, 1]`). (1) For nonempty disjoint `A, B`, an `α`-approximate
`f` on `A` and a `β`-approximate `g` on `B` with `γ := max{α, β} + 1 ≤ log n`, every
convolution `h = f ⊕ g` is `γ`-approximate on `A ∪ B`. (2) Moreover one admissible program and
one constant `C` compute, from the explicit tables of any `A`-function `f` and `B`-function `g`
(layout `ConvInput`), the table of some `f ⊕ g` (address in `N[5]`) within
`C · (log₂(n/η)/ε)^{C d}` steps. -/
theorem claim_4_11 :
    (∀ (d n k : ℕ), 2 ≤ d → n = 2 ^ k → 1 ≤ k → ∀ I : Items d n, I.Nonneg →
      ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
      ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
      ∀ (A B : Finset (Fin n)), A.Nonempty → B.Nonempty → Disjoint A B →
      ∀ (α β : ℝ) (f g h : AFun d n),
        IsApproxOn I Wt ε η α A f → IsApproxOn I Wt ε η β B g → max α β + 1 ≤ (k : ℝ) →
        IsConv I Wt ε η A B f g h → IsApproxOn I Wt ε η (max α β + 1) (A ∪ B) h) ∧
    (∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n k : ℕ), 2 ≤ d → n = 2 ^ k → 1 ≤ k → ∀ I : Items d n, I.Nonneg →
      ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
      ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
      ∀ (A B : Finset (Fin n)), A.Nonempty → B.Nonempty → Disjoint A B →
      ∀ f g : AFun d n, IsAFun I Wt ε η A f → IsAFun I Wt ε η B g →
      ∀ s₀ : State, ConvInput I Wt ε η A B f g s₀ →
        RunsWithin P s₀ (C * (Real.logb 2 ((n : ℝ) / η) / ε) ^ (C * (d : ℝ)))
          (fun s => ∃ h : AFun d n, IsConv I Wt ε η A B f g h ∧
            TableRep I Wt ε η s (s.N 5) (A ∪ B) h)) := by sorry

end VecKnapsackMitM.Main
