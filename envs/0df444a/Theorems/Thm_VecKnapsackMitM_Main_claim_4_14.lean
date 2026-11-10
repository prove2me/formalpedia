-- Prove2me | Theorems.Thm_VecKnapsackMitM_Main_claim_4_14
-- name    : VecKnapsackMitM.Main.claim_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:35:25.668718+00:00
-- url     : https://prove2.me/theorems/75af1f81-b259-4fe5-a1f5-e0f2e816c752
-- title:
--   Claim 4.14 — $\log n$-approximate functions on all suffixes in time $n(\log(n/\eta)/\varepsilon)^{O(d)}$
-- statement:
--   Setting of the proof of Lemma 4.8 ($d\ge2$, $n=2^k\ge2$, nonnegative items, $\bar W_2,\dots,\bar W_{d-1}\ge0$, $\varepsilon,\eta\in(0,1]$, $\delta$, $\Delta$ as there). There are one admissible real-RAM program and one absolute constant $C$ such that from the input `sec45Input` the program halts within $C\cdot n\cdot(\log_2(n/\eta)/\varepsilon)^{C\cdot d}$ steps and, for every $i\in[n]$, the address in $N[2+i-1]$ holds the table of a function $f_i$ that is $\log n$-approximate on $I_i=\{i,\dots,n\}$.
--
--   Differences from the source:
--   - encoding: the setting of the proof of Lemma 4.8: n ≥ 2 a power of two, δ := ε/(10 log n), ∆ := (εη/(10n))^5, fixed W̄_2, …, W̄_{d−1}, ε, η ∈ (0, 1] → hypotheses n = 2^k with 1 ≤ k, nonnegative items and middle estimates, ε, η ∈ (0, 1]; δ and ∆ are the definitions cDelta, cBigDelta; log n = k; reason: the claims are stated inside that proof, which fixes these objects; nothing is added
--   - encoding: vectors x ∈ ℝ^d_{≥0} with x_0 the profit and x_1, …, x_{d−1} weights; R^J ⊆ ℝ^d → PVec d with prof = x_0 and wt t = x_{t+1} for t + 1 < d; the unused coordinate wt (d − 1) is 0 on R^J (InDom); reason: zero-based weight indices; R^J is the same finite set
--   - encoding: an A-function maps x ∈ R^A to ⊥ or a virtual item with set ⊆ A; p(⊥) = ∞, w̄(⊥) = −∞ → AFun d n := PVec d → Option (Finset (Fin n)), none for ⊥ and the represented set otherwise; properties 1–3 of Definition 4.10 are required only when the value is not ⊥; reason: a virtual item is used only through p, w̄ and set, which are those of its set; at ⊥ properties 1–3 hold by the ∞ conventions, so requiring them only off ⊥ is the same definition
--   - encoding: Definition 4.10 for real γ ≥ 0 → γ : ℝ with 0 ≤ γ in IsApproxOn; real powers in QSet; dyadic depths are cast to ℝ; reason: retains all nonnegative real approximation levels of Definition 4.10 and Claim 4.11, including noninteger levels
--   - encoding: "compute functions" (explicit tables, proof of Claim 4.13) → tables in memory (TableRep: a list of entries whose keys are exactly the points of R^J, each with ⊥ or a virtual item record); reason: the paper stores the functions explicitly; a table is the machine form of that
--   - encoding: "for all i ∈ [n] we can compute functions f_i" → the table of f_i (paper index i = Lean i + 1) at the address in N[2 + i] (0-based i), on suffix n i; reason: one output cell per suffix
--   - generalization: an algorithm on the RealRAM (§2, printed p. 8) → an admissible program (VecBalPoly.Admissible: rational literals, no √, no random draws) of the published unit-cost real RAM MatMulTimeLP, which has no floor, no real-to-index conversion and no index multiplication; time = executed instructions including the final halt; reason: fewer primitives only make the existential claim harder; every such program is a deterministic RealRAM algorithm with the same step count, so the Lean statement specializes to the paper's
--   - reading: "in time …^{O(d)}" for given parameters → one program P and one absolute constant C, chosen before d, the error parameters and the input; the O(d) exponent is C·d; reason: the bounds are stated for all d, so the constant in O(d) is absolute; one procedure taking the parameters as input is the stronger of the two readings and is what the paper describes
--   - reading: "in time X" (no explicit O) → at most C·X executed instructions, with the same absolute C as in the exponent; reason: ordinary asymptotic running-time notation permits an absolute leading constant; this does not resolve the separate dimension-uniform base-one issue in INSIGHTS I3, whose printed formulas are retained
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Claim 4.14, printed p. 27 (PDF 28)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Definitions.Def_VecKnapsackMitM_Main_Convolution

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-- Bringmann, Kulik, Węgrzycki (2026), Claim 4.14, printed p. 27 (PDF 28), in the setting of
the proof of Lemma 4.8 (`n = 2^k ≥ 2`). One admissible program and one constant `C` such that
from the input `sec45Input` the program halts within `C · n · (log₂(n/η)/ε)^{C d}` steps with,
for every `i ∈ [n]`, the explicit table (address in `N[2 + i]`, 0-based `i`) of a function `f_i`
that is `log n`-approximate on `I_i = {i, …, n}`. -/
theorem claim_4_14 :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n k : ℕ), 2 ≤ d → n = 2 ^ k → 1 ≤ k → ∀ I : Items d n, I.Nonneg →
      ∀ Wt : Fin d → ℝ, (∀ t : Fin d, 1 ≤ t.val → t.val + 2 ≤ d → 0 ≤ Wt t) →
      ∀ (ε η : ℝ), 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 →
        RunsWithin P (sec45Input I Wt ε η)
          (C * n * (Real.logb 2 ((n : ℝ) / η) / ε) ^ (C * (d : ℝ)))
          (fun s => ∀ i : Fin n,
            ∃ f : AFun d n, TableRep I Wt ε η s (s.N (2 + i.val)) (Items.suffix n i.val) f ∧
              IsApproxOn I Wt ε η k (Items.suffix n i.val) f) := by sorry

end VecKnapsackMitM.Main
