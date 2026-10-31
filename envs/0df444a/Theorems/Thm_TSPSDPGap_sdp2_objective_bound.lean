-- Prove2me | Theorems.Thm_TSPSDPGap_sdp2_objective_bound
-- name    : TSPSDPGap.sdp2_objective_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:35.364629+00:00
-- url     : https://prove2.me/theorems/446ad184-b47c-4cb2-8a52-5d375e98bbbb
-- title:
--   Proof of Theorem 4.1, (5)–(7) — the SDP (2) objective of $Y$ is at most $\tilde c_g/n+2$
-- statement:
--   Let $g\ge2$ be even. There is a constant $\tilde c_g$, depending on $g$ but not on $n$, such that for every $n$ with $g\mid n$ and $g<n$, every $r\in[n+1]$ and every choice $s\in[n+1]$ of the extra vertex of the $(n+1)$-vertex simplicial instance $D$,
--   $$
--   \operatorname{trace}\Bigl(\bigl(D[\beta]\otimes\tfrac12C^{(n+1)}_1[\alpha]+\operatorname{Diag}(\bar c)\bigr)Y\Bigr)\le\frac{\tilde c_g}{n}+2,
--   $$
--   where $\alpha=[n+1]\setminus\{r\}$, $\beta=[n+1]\setminus\{s\}$, $\bar c=\operatorname{vec}(C_1[\alpha,\{r\}]D[\{s\},\beta])$ and $Y$ is the solution (3), feasible for SDP (2).
--
--   The paper obtains it from (5) by bounding the first term with Theorem 4.21, (6), and the diagonal term by $2$, (7). With $\mathrm{OPT}_{\mathrm{TSP}}=g$ it gives the ratio $g/(2+\tilde c_g/n)\to g/2$.
--
--   **Formalization Note** The constant is quantified before $n$, $r$ and $s$.
--
--   Differences from the source:
--   - generalization: s = r = 1 → every r, s ∈ Fin (n + 1), the extra vertex of the instance being s; reason: (6) holds for every r because C₁^(n+1)[α] ≤ C₁^(n) entrywise for every deleted r, and (7) because the column C₁[α,{r}] has two ones; s only relabels the instance; specializes at r = s = 0
--   - reading: c̄ = vec(C₁[α, {r}] D[{s}, β]) (p.7; p.28 prints C₁^(n)[α, {1}]) → C₁ = C₁^(n+1); reason: α ⊆ [n + 1], so only C₁^(n+1)[α, {r}] is defined; its value e₁ + eₙ is the one p.28 computes
--   - encoding: α = [n+1]∖r, β = [n+1]∖s; vec stacks columns → Fin.succAbove r, Fin.succAbove s; Matrix.vec (index (column, row)); reason: Lean convention; orientation checked on a 4-city instance in Solutions/verification/TSPSDPGap_lift.lean
--   - encoding: standing assumptions of §4: g even, g groups of n/g vertices, a_i and b_i with denominators g, g − 1, n − g → hypotheses Even g, 2 ≤ g, g ∣ n, g < n; reason: the section's standing assumption (g even) plus the conditions under which (3) and a_i, b_i are defined; given g ∣ n they exclude only n/g ∉ ℕ, g ∈ {0, 1} and n − g = 0
--   - encoding: Y = 1/(2n)[(J_g − I_g) ⊗ J_{n/g} ⊗ B + I_g ⊗ J_{n/g} ⊗ A + I_g ⊗ I_{n/g} ⊗ (2I_n − A)] (3) → Ymat g n, entrywise: block (p, q) is (1/(2n))·2I_n if p = q, (1/(2n))A if p ≠ q lie in the same group ⌊p/(n/g)⌋, (1/(2n))B otherwise; reason: equal to (3) reindexed by Fin g × Fin (n/g) ≃ Fin n (proved: Solutions/verification/TSPSDPGap_sanity.lean, Ymat_eq_eq3); same matrix
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, proof of Theorem 4.1, (5)–(7), pp.27–28

import Mathlib
import Definitions.Def_TSPSDPGap_sdp2Objective
import Definitions.Def_TSPSDPGap_simplicialCostExt
import Definitions.Def_TSPSDPGap_Ymat

namespace TSPSDPGap

/-- **Proof of Theorem 4.1, (5)–(7): the SDP (2) objective of `Y` on the extended instance is at most `c̃_g/n + 2`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, proof of Theorem 4.1, pp.27–28: "(6) trace((D[β] ⊗ ½C^(n+1)_1[α])Y) ≤
½ trace((((J_g − I_g) ⊗ J_(n/g)) ⊗ (C^(n)_1))Y) ≤ c̃_g/n … (7) trace(Diag(c̄)Y) ≤ 2n ∗ 1/n = 2.
Plugging Equations (6) and (7) into Equation (5) we obtain
trace((D[β] ⊗ ½C^(n+1)_1[α] + Diag(c̄))Y) ≤ c̃_g/n + 2."

For every even `g ≥ 2` there is one constant `c`, chosen before `n`, such that for every `n`
with `g ∣ n`, `g < n`, every `r` and every extra vertex `s`, the SDP (2) objective of `Y` on the
`(n + 1)`-vertex simplicial instance is at most `c / n + 2`.

**Formalization Note.** The objective is `sdp2Objective n D r s Y` with
`D = simplicialCostExt g n s` and `Y = Ymat g n`. The paper takes `r = s = 1` (`= 0` here); the
statement covers every `r` and every `s`. `∃ c` precedes `∀ n`. -/
theorem sdp2_objective_bound (g : ℕ) (hg : Even g) (hg2 : 2 ≤ g) :
    ∃ c : ℝ, ∀ n : ℕ, g ∣ n → g < n → ∀ r s : Fin (n + 1),
      sdp2Objective n (simplicialCostExt g n s) r s (Ymat g n) ≤ c / n + 2 := by sorry

end TSPSDPGap
