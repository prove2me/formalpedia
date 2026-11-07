-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_34
-- name    : PolyEulerFlow.lemma_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:52.877701+00:00
-- url     : https://prove2.me/theorems/45fa6bc9-1c66-4a65-9dd4-b663c2f3169c
-- title:
--   Lemma 34 — comparator estimates
-- statement:
--   Consider the comparator recursion
--   $$v^+=v+\eta\Big((1-p)\frac{v-v^3}{2}+p(u-v)\Big)+\eta\xi_v,\qquad|\xi_v|\le\nu,$$
--   on the scalar box ($-\nu\le p\le1+\nu$, $|v|\le1+4\nu$), with $|u|\le1$, where the gate $p$ and the test value $u$ are given sequences. Write $h=2^{-s}$, $\varepsilon=h^K$, $L=\log(1/\varepsilon)$, $\vartheta=7/8$.
--
--   1. **Cone preservation.** There is $c_0>0$ such that: if $u\ge m>0$ on an interval, $0<r\le m/4$, $r\le1/4$ and $\nu<c_0r$, then $v\ge r$ at the start of the interval implies $v\ge r$ throughout it; and if $u\le-m$, then $v\le-r$ is preserved.
--   2. **Purification during a comparison phase.** For every fixed $K\ge256$ and $c,c'>0$ and every envelope constant $C_{env}>0$ there are $C$, $D$ and $s_0$ such that for $s\ge s_0$ and $0\le\nu\le\varepsilon^2$: if $u\ge m\ge ch$, $v(0)\ge c'h$ and the gate satisfies the envelope of the old gate of Lemma 31, $|p(t)|\le C_{env}e^{-3t/8}+C_{env}\varepsilon^{37/20}+C_{env}\nu$, up to the cut (the first grid time $\ge\vartheta L$), then at the cut $|v-1|\le C\varepsilon^{1/4}$, and $v\ge1/2$ is reached by time $D+9\log(1/h)+C$.
--   3. **Retention under small tracking mass.** There are $C,\delta_0>0$ such that if $|v(a)-\sigma|\le d$ with $\sigma\in\{-1,1\}$ and $d+\int_a^b|p|\,d\eta t+(b-a)\nu\le\delta_0$, then $\sup_{a\le t\le b}|v(t)-\sigma|\le C\big(d+\int_a^b|p|\,d\eta t+(b-a)\nu\big)$, whatever the sign of $u$.
--   4. **Preparation under an open tracking gate.** For every fixed $K\ge256$ and $c>0$ there are $C$ and $s_0$ such that for $s\ge s_0$, $0\le\nu\le\varepsilon^2$: if $p\ge9/10$ and $u\ge m\ge ch$ up to time $2\log(1/h)+C$, then from any value of $v$ in its box, $v\ge m/2$ is reached within time $2\log(1/h)+C$, and afterwards $v\ge m/4$ is preserved as long as $u\ge m$, whatever the gate does in its permitted interval.
--
--   These are the three uses of a comparator in a cycle: it purifies to the sign of its test, retains that sign while its gate is closed, and prepares a new sign when the gate opens.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - reading: for any fixed positive margin constant m; ν smaller than a fixed constant times r → c₀ existential before m and r; ∀ m > 0; ν < c₀ r; reason: the strongest order of the printed quantifiers
--   - reading: u ≥ m ≥ ch, v(0) ≥ c′h, and the tracking gate satisfies the envelope of the old gate of Lemma 31 → ∀ c, c′ > 0 and every envelope constant C_env > 0, with C, D, s₀ chosen after them; the hypotheses on u and p imposed up to the cut; reason: Lemma 31's C_env is one of these constants, and only the times up to the cut influence the conclusion
--   - reading: at the time ϑL + O(1) of the cut → at the cut index, the first grid time ≥ ϑL; reason: this is the cut t^cut_j of §6.6 (p.30), at time ϑL + O(1)
--   - reading: after a bounded initial delay, it takes at most a time 9 log(1/h) + C to reach v ≥ 1/2 → ∃ D ≥ 0 and a grid time t_k ≤ D + 9 log(1/h) + C with v_k ≥ 1/2; reason: the delay is a constant fixed with C
--   - reading: d + ∫|p| dηt + (b − a)ν is sufficiently small → ≤ δ₀ for an existential δ₀ > 0; reason: standard reading of 'sufficiently small'
--   - reading: If p ≥ 9/10 and u ≥ m ≥ ch … the resulting smaller cone (for example v ≥ m/4) is preserved → hypotheses on p and u up to time 2 log(1/h) + C; then v ≥ m/4 at every later index as long as u ≥ m; reason: the printed example cone m/4 is taken
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 34, p.31 (PDF 33)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsUniformClock

namespace PolyEulerFlow

/-- **Lemma 34 (Comparator estimates)**, p.31 (PDF 33). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

For the comparator `v⁺ = v + η((1 - p)(v - v³)/2 + p(u - v)) + ηξ_v`, `|ξ_v| ≤ ν`, on the scalar box, with `|u| ≤ 1`:
1. *Cone preservation.* If `u ≥ m > 0` on an interval, `0 < r ≤ m/4`, `r ≤ 1/4` and `ν < c₀ r` for a fixed constant `c₀`, then `v ≥ r` is invariant
   on that interval; reflected for a negative test.
2. *Purification.* For every fixed `K ≥ 256` and `c, c′ > 0` (and the envelope constant of the old gate): if `u ≥ m ≥ ch`, `v(0) ≥ c′h` and the
   gate satisfies `|p(t)| ≤ C_env e^{-3t/8} + C_env ε^{37/20} + C_env ν`, then at the cut (the first grid time `≥ ϑL`, `ϑ = 7/8`) `|v - 1| ≤ Cε^{1/4}`,
   and `v ≥ 1/2` is reached within time `D + 9 log(1/h) + C`.
3. *Retention.* If `|v(a) - σ| ≤ d`, `σ ∈ {-1, 1}`, and `d + ∫_a^b |p| dηt + (b - a)ν ≤ δ₀`, then `|v(t) - σ| ≤ C(d + ∫_a^b |p| dηt + (b - a)ν)` for
   `a ≤ t ≤ b`, whatever the sign of `u`.
4. *Preparation.* If `p ≥ 9/10` and `u ≥ m ≥ ch`, then from any value in the box, `v ≥ m/2` is reached within time `2 log(1/h) + C`, and afterwards
   `v ≥ m/4` is preserved as long as `u ≥ m`, whatever the gate does in its permitted interval.

**Formalization Note** `u` and `p` are given sequences. The hypotheses on `u` and `p` are imposed on the time window the conclusion concerns.
"A bounded initial delay" is an existential constant `D`; "sufficiently small" is an existential `δ₀`. The mesh is variable (Corollary 39, p.34),
which contains every constant mesh. In 2 and 4, `h = 2^{-s}`, `ε = h^K`, `0 ≤ ν ≤ ε²` and `s` is above a threshold `s₀`. -/
theorem lemma_34 :
    -- 1. cone preservation
    (∃ c0 : ℝ, 0 < c0 ∧
      ∀ ν m r : ℝ, 0 < m → 0 < r → r ≤ m / 4 → r ≤ 1 / 4 → 0 ≤ ν → ν < c0 * r →
      ∀ η p u ξv v : ℕ → ℝ, IsComparatorOrbit ν η p u ξv v → ∀ a b : ℕ, a ≤ b →
        ((∀ k, a ≤ k → k < b → m ≤ u k) → r ≤ v a → ∀ k, a ≤ k → k ≤ b → r ≤ v k) ∧
        ((∀ k, a ≤ k → k < b → u k ≤ -m) → v a ≤ -r → ∀ k, a ≤ k → k ≤ b → v k ≤ -r)) ∧
    -- 2. purification during a comparison phase
    (∀ K : ℕ, 256 ≤ K → ∀ c c' Cenv : ℝ, 0 < c → 0 < c' → 0 < Cenv →
      ∃ (C D : ℝ) (s0 : ℕ), 0 < C ∧ 0 ≤ D ∧
      ∀ s : ℕ, s0 ≤ s →
        let h := scale s
        let ε := h ^ K
        let L := Real.log (1 / ε)
        ∀ ν m : ℝ, 0 ≤ ν → ν ≤ ε ^ 2 → c * h ≤ m →
        ∀ η p u ξv v : ℕ → ℝ, IsComparatorOrbit ν η p u ξv v →
          let t := physTime η
          let kcut := firstGrid η ((7 / 8) * L)
          (∀ k, k ≤ kcut → m ≤ u k) → c' * h ≤ v 0 →
          (∀ k, k ≤ kcut →
            |p k| ≤ Cenv * Real.exp (-(3 / 8) * t k) + Cenv * ε ^ ((37 : ℝ) / 20) + Cenv * ν) →
          |v kcut - 1| ≤ C * ε ^ ((1 : ℝ) / 4) ∧
          ∃ k, t k ≤ D + 9 * Real.log (1 / h) + C ∧ 1 / 2 ≤ v k) ∧
    -- 3. retention under small tracking mass
    (∃ C δ0 : ℝ, 0 < C ∧ 0 < δ0 ∧
      ∀ ν d σ : ℝ, 0 ≤ ν → (σ = 1 ∨ σ = -1) →
      ∀ η p u ξv v : ℕ → ℝ, IsComparatorOrbit ν η p u ξv v → ∀ a b : ℕ, a ≤ b →
        let mass := d + gridSum η (fun k => |p k|) a b + (physTime η b - physTime η a) * ν
        |v a - σ| ≤ d → mass ≤ δ0 → ∀ k, a ≤ k → k ≤ b → |v k - σ| ≤ C * mass) ∧
    -- 4. preparation under an open tracking gate
    (∀ K : ℕ, 256 ≤ K → ∀ c : ℝ, 0 < c →
      ∃ (C : ℝ) (s0 : ℕ), 0 < C ∧
      ∀ s : ℕ, s0 ≤ s →
        let h := scale s
        let ε := h ^ K
        ∀ ν m : ℝ, 0 ≤ ν → ν ≤ ε ^ 2 → c * h ≤ m →
        ∀ η p u ξv v : ℕ → ℝ, IsComparatorOrbit ν η p u ξv v →
          let t := physTime η
          (∀ k, t k ≤ 2 * Real.log (1 / h) + C → 9 / 10 ≤ p k ∧ m ≤ u k) →
          ∃ k, t k ≤ 2 * Real.log (1 / h) + C ∧ m / 2 ≤ v k ∧
            ∀ k', k ≤ k' → (∀ i, k ≤ i → i < k' → m ≤ u i) → m / 4 ≤ v k') := by sorry

end PolyEulerFlow
