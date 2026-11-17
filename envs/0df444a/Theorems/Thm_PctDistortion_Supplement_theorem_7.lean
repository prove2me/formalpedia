-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_7
-- name    : PctDistortion.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:32:11.10189+00:00
-- url     : https://prove2.me/theorems/521f21a5-813a-4cf0-9f5f-2f3286cbac19
-- title:
--   Theorem 7 — every randomized voting rule has α-percentile distortion $\ge 5-2\lfloor\alpha m+2\rfloor/m$, tending to $5-2\alpha$
-- statement:
--   Fix $\alpha\in[1/2,1)$. For every $m\ge1$ and every randomized voting rule $A$ there is an election $\mathcal E$ with $m$ candidates such that
--   $$\mathrm{dist}^\alpha_{\mathcal E}(A(\mathcal E))\ \ge\ 5-\frac{2\lfloor\alpha m+2\rfloor}{m},$$
--   and
--   $$\lim_{m\to\infty}\Big(5-\frac{2\lfloor\alpha m+2\rfloor}{m}\Big)=5-2\alpha.$$
--
--   This is the first lower bound on randomized α-percentile distortion for every $\alpha\in[1/2,1)$; for the median ($\alpha=1/2$) it improves the previous bound $3$ to $4-4/m$.
--
--   Differences from the source:
--   - reading: the α-percentile distortion of every randomized voting rule is at least 5 − 2⌊αm + 2⌋/m (m the number of candidates) → for every m ≥ 1 and every rule A, some election with exactly m candidates has distortion of A(E) at least the bound; reason: the distortion of a rule is the supremum over elections, and the bound depends on the number of candidates; the number of voters is left free
--   - encoding: distortion as a supremum of real ratios → the published ℝ≥0∞-valued distortion, bound written as ENNReal.ofReal; reason: ℝ≥0∞ ratio with x/0 = ⊤ (x > 0), 0/0 = 0; distortion ≤ B iff the cost inequality holds for every consistent metric, as in the paper
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 7, p.22 (proof App. F.1, pp.40–42; = Theorem A, part 1, p.3)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_Supplement_IsRandomizedRule

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion Filter Topology

/-- **Theorem 7** (general lower bound). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 7, p.22 (proof App. F.1, pp.40–42;
= Theorem A, part 1, p.3): "For every α ∈ [1/2, 1), the α-percentile distortion of every
randomized voting rule is at least 5 − 2⌊αm + 2⌋/m, which converges to 5 − 2α as m → ∞."

Here `m` is the number of candidates: for every `m ≥ 1` and every randomized voting rule `A`
there is an election with `m` candidates on which `A` has distortion at least
`5 − 2⌊αm + 2⌋/m`; and this bound tends to `5 − 2α`.

**Formalization Note.** The distortion of a rule is the supremum over elections, so a lower bound
on it is an election attaining the bound. The number of voters is not fixed. `A` is any map from
elections to lotteries (`IsRandomizedRule`), with no neutrality or anonymity. -/
theorem theorem_7 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) :
    (∀ m : ℕ, 1 ≤ m → ∀ A : VotingRule, IsRandomizedRule A →
      ∃ (V C : Type) (_ : Fintype V) (_ : Nonempty V) (_ : Fintype C) (_ : Nonempty C)
        (E : Election V C), Fintype.card C = m ∧
        ENNReal.ofReal (5 - 2 * (⌊α * (m : ℝ) + 2⌋₊ : ℝ) / (m : ℝ)) ≤ distortion α E (A V C E)) ∧
    Tendsto (fun m : ℕ => 5 - 2 * (⌊α * (m : ℝ) + 2⌋₊ : ℝ) / (m : ℝ)) atTop
      (𝓝 (5 - 2 * α)) := by sorry

end PctDistortion.Supplement
