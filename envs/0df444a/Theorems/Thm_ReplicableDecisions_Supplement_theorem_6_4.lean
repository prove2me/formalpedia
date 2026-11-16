-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_4
-- name    : ReplicableDecisions.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:09:32.703927+00:00
-- url     : https://prove2.me/theorems/f575509e-76c2-41ff-adfd-ddde881ac63e
-- title:
--   Theorem 6.4 — Hellinger-isometric experiments with different decision costs
-- statement:
--   Let $b\ge1$, $M=2^b$ and $0<\varepsilon\le1/4$, and put $a=(\sqrt{1+2\varepsilon}+\sqrt{1-2\varepsilon})/2$. There are absolute constants $C_1,\dots,C_8>0$ such that for all such $b,\varepsilon$ there are experiments $\mathcal E_{\mathrm{hard}}=(\{P_0,\dots,P_{M-1}\},\Gamma)$ and $\mathcal E_{\mathrm{easy}}=(\{Q_0,\dots,Q_{M-1}\},\Gamma)$ on alphabets of size $M$, with $\Gamma(0)=\{0\}$ and $\Gamma(i)=\{1\}$ for $i\ge1$, such that:
--   1. every probability in both experiments is strictly positive, $h(P_i,P_j)=h(Q_i,Q_j)$ for all $0\le i,j<M$, and $h(P_i^{\otimes n},P_j^{\otimes n})=h(Q_i^{\otimes n},Q_j^{\otimes n})$ for every $n\ge1$;
--   2. for $0<\beta\le1/8$, $0<\rho\le1/16$ and $\xi=\min\{\beta,\rho\}$,
--   $$n^\star_{\mathrm{hard}}=\Theta\Big(\varepsilon^{-2}\log\frac M\xi\Big),\quad n^\star_{\mathrm{easy}}=\Theta\Big(\varepsilon^{-2}\log\frac1\xi\Big),$$
--   $$n^\star_{\mathrm{str,hard}}=\Theta\Big(\varepsilon^{-2}\Big[\rho^{-2}+\log\frac M\beta\Big]\Big),\quad n^\star_{\mathrm{str,easy}}=\Theta\Big(\varepsilon^{-2}\Big[\rho^{-2}+\log\frac1\beta\Big]\Big),$$
--   with the absolute constants $C_1,\dots,C_8$;
--   3. both experiments have $s_L^2=1-a$ for every $L\ge1$, every local Hellinger packing number agrees under $i\leftrightarrow i$, and $\mathsf D_\rho=\log M$ in both.
--
--   Moreover, the weak upper bound for the easy experiment is achieved by a deterministic test that processes each sample only through membership in one fixed event $E$: output $1$ iff $\#\{r:Z_r\in E\}\ge t$, with $n\le C_4\varepsilon^{-2}\log(1/\xi)$ samples.
--
--   Hence the labeled Hellinger distance matrix, even with all its tensor powers, does not determine the optimal sample size within constant factors.
--
--   Differences from the source:
--   - encoding: {P_0, …, P_{M−1}}, Γ(0) = {0}, Γ(i) = {1}, alphabets of size M → models indexed by Fin (2^b), Γ i = {false} iff i = 0 else {true}; alphabets Zh, Ze : Type with card 2^b; reason: Lean indexing
--   - encoding: Θ(·) in (6.3)–(6.4), "All implicit constants are absolute" → ∃ C₁ … C₈ > 0 before b and ε, one pair per Θ, with C·F ≤ N ≤ C′·F for the least elements N of validSampleSizes / strongValidSampleSizes; reason: the Lean reading of Θ
--   - reading: "Every local Hellinger packing number, including the profile defining D_ρ, is identical under the indicated correspondence of models. In fact D_ρ = log M in both experiments." → ∀ i and r, η > 0, pack Eh i r η = pack Ee i r η, and for every ρ > 0, localDim at s_ρ/9 equals log M in both; reason: packing numbers are indexed by the center, radius and resolution, defined for r, η > 0 (p.32); D_ρ is defined for every ρ > 0
--   - reading: "achieved by a deterministic test that processes each sample only through membership in one event" → ∃ one event Ev of the easy alphabet such that for all β, ρ in range ∃ n ≤ C₄ ε⁻² log(1/ξ) and t with x ↦ 1{#{r : x_r ∈ Ev} ≥ t} (trivial seed) (β, ρ)-valid on E_easy; reason: C₄ is the easy weak upper constant, so this rule achieves that bound
--   - reading: "and uses O(n) integer additions and one threshold comparison" → not formalized; reason: names no machine model; implementation remark, as for the published Theorem 3.2
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.4, (6.3)–(6.4), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_Supplement_strongValidSampleSizes
import Definitions.Def_ReplicableDecisions_Supplement_localDim

open MeasureTheory

namespace ReplicableDecisions.Supplement

open Classical in
/-- **Theorem 6.4 (Hellinger-isometric experiments).** Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 6.4, (6.3)–(6.4), p.29 (PDF p.31).
Let `b ≥ 1`, `M = 2^b`, `0 < ε ≤ 1/4`. There are experiments `E_hard = ({P₀, …, P_{M−1}}, Γ)` and
`E_easy = ({Q₀, …, Q_{M−1}}, Γ)` on alphabets of size `M`, with `Γ(0) = {0}` and `Γ(i) = {1}` for
`i ≥ 1`, such that:
1. every probability in both is strictly positive, `h(P_i, P_j) = h(Q_i, Q_j)` for all `i, j`, and
   the same holds for the `n`-fold products for every `n ≥ 1`;
2. uniformly for `0 < β ≤ 1/8`, `0 < ρ ≤ 1/16`, with `ξ = min{β, ρ}`,
   `n⋆_hard = Θ(ε⁻² log(M/ξ))`, `n⋆_easy = Θ(ε⁻² log(1/ξ))`,
   `n⋆_str,hard = Θ(ε⁻²[ρ⁻² + log(M/β)])`, `n⋆_str,easy = Θ(ε⁻²[ρ⁻² + log(1/β)])`, all implicit
   constants absolute;
3. both have `s_L² = 1 − a` for every `L ≥ 1`, `a = (√(1 + 2ε) + √(1 − 2ε))/2`; every local
   Hellinger packing number is identical under the correspondence of models, and `D_ρ = log M` in
   both.
The weak upper bound for the easy experiment is achieved by a deterministic test that processes each
sample only through membership in one event.

**Formalization Note.** Models are indexed by `Fin M`, index `0` forced to `0 = false`. The eight
constants are quantified before `b` and `ε`. The deterministic test is `1{#{r : x_r ∈ Ev} ≥ t}` for
one event `Ev` of the easy alphabet (fixed before `β, ρ`), with a trivial seed, at a sample size
within the easy upper bound `C₄ ε⁻² log(1/ξ)`; the "`O(n)` integer additions" count is not
formalized. `D_ρ = log M` is asserted for every `ρ > 0`. -/
theorem theorem_6_4 :
    ∃ C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < C₄ ∧ 0 < C₅ ∧ 0 < C₆ ∧
      0 < C₇ ∧ 0 < C₈ ∧
      ∀ (b : ℕ), 1 ≤ b → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
        let Γ : Fin (2 ^ b) → Set Bool := fun i => if (i : ℕ) = 0 then {false} else {true}
        let a : ℝ := (Real.sqrt (1 + 2 * ε) + Real.sqrt (1 - 2 * ε)) / 2
        let M : ℝ := (2 : ℝ) ^ b
        ∃ (Zh : Type) (_ : Fintype Zh) (Ze : Type) (_ : Fintype Ze)
          (Eh : Experiment (Fin (2 ^ b)) Zh) (Ee : Experiment (Fin (2 ^ b)) Ze),
          Fintype.card Zh = 2 ^ b ∧ Fintype.card Ze = 2 ^ b ∧
          -- property 1
          (∀ i z, 0 < Eh.P i z) ∧ (∀ i z, 0 < Ee.P i z) ∧
          (∀ i j, hellinger (Eh.P i) (Eh.P j) = hellinger (Ee.P i) (Ee.P j)) ∧
          (∀ n : ℕ, 1 ≤ n → ∀ i j,
            hellinger (productLaw (n := n) (Eh.P i)) (productLaw (n := n) (Eh.P j)) =
              hellinger (productLaw (n := n) (Ee.P i)) (productLaw (n := n) (Ee.P j))) ∧
          -- property 3
          (∀ L : ℕ, 1 ≤ L → hopSeparation Eh Γ L ^ 2 = 1 - a ∧ hopSeparation Ee Γ L ^ 2 = 1 - a) ∧
          (∀ i (r η : ℝ), 0 < r → 0 < η → pack Eh i r η = pack Ee i r η) ∧
          (∀ ρ : ℝ, 0 < ρ →
            localDim Eh (hopSeparation Eh Γ (hopBudget ρ) / 9) = Real.log M ∧
            localDim Ee (hopSeparation Ee Γ (hopBudget ρ) / 9) = Real.log M) ∧
          -- property 2 and the one-event test
          ∃ Ev : Set Ze, ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
            let ξ : ℝ := min β ρ
            (∃ N : ℕ, IsLeast (validSampleSizes Eh Γ β ρ) N ∧
              C₁ * (1 / ε ^ 2 * Real.log (M / ξ)) ≤ (N : ℝ) ∧
              (N : ℝ) ≤ C₂ * (1 / ε ^ 2 * Real.log (M / ξ))) ∧
            (∃ N : ℕ, IsLeast (validSampleSizes Ee Γ β ρ) N ∧
              C₃ * (1 / ε ^ 2 * Real.log (1 / ξ)) ≤ (N : ℝ) ∧
              (N : ℝ) ≤ C₄ * (1 / ε ^ 2 * Real.log (1 / ξ))) ∧
            (∃ N : ℕ, IsLeast (strongValidSampleSizes Eh Γ β ρ) N ∧
              C₅ * (1 / ε ^ 2 * (1 / ρ ^ 2 + Real.log (M / β))) ≤ (N : ℝ) ∧
              (N : ℝ) ≤ C₆ * (1 / ε ^ 2 * (1 / ρ ^ 2 + Real.log (M / β)))) ∧
            (∃ N : ℕ, IsLeast (strongValidSampleSizes Ee Γ β ρ) N ∧
              C₇ * (1 / ε ^ 2 * (1 / ρ ^ 2 + Real.log (1 / β))) ≤ (N : ℝ) ∧
              (N : ℝ) ≤ C₈ * (1 / ε ^ 2 * (1 / ρ ^ 2 + Real.log (1 / β)))) ∧
            ∃ n t : ℕ, (n : ℝ) ≤ C₄ * (1 / ε ^ 2 * Real.log (1 / ξ)) ∧
              IsValid Ee Γ β ρ (Measure.dirac ())
                (fun (x : Fin n → Ze) (_ : Unit) =>
                  decide (t ≤ (Finset.univ.filter (fun r => x r ∈ Ev)).card)) := by sorry

end ReplicableDecisions.Supplement
