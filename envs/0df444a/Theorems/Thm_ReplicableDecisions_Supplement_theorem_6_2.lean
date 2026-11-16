-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_2
-- name    : ReplicableDecisions.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:08:18.164367+00:00
-- url     : https://prove2.me/theorems/7417e9ca-1497-4f97-a335-6c1651ab154d
-- title:
--   Theorem 6.2 — noisy parities: the logarithm at every scale
-- statement:
--   For $u,x\in\mathbb F_2^b$ write $\chi_u(x)=(-1)^{u\cdot x}$. For an integer $b\ge1$ and $0<\varepsilon\le1/2$, consider the experiment on $\mathbb F_2^b$ consisting of the uniform law $P_*$, forced to answer $0$, and the $2^b-1$ laws $P_u(x)=2^{-b}(1+2\varepsilon\chi_u(x))$, $u\ne0$, forced to answer $1$.
--
--   There are universal constants $C_1,C_2>0$ such that, for every $b\ge1$ and $0<\varepsilon\le1/2$: the experiment has $M=2^b$ models and no indifference models; $\varepsilon^2/2\le s_L^2\le6\varepsilon^2/5$ for every $L\ge1$; and for $0<\beta\le1/8$ and $0<\rho\le1/16$,
--   1. every $(\beta,\rho)$-valid algorithm uses at least $b\log2/(4\varepsilon^2)$ samples;
--   2. $\displaystyle\frac1{45\varepsilon^2}\log\frac M{\min\{\beta,\rho\}}\le n^\star(\beta,\rho)\le\Big\lceil\frac6{\varepsilon^2}\log\frac M{\min\{\beta,\rho\}}\Big\rceil$;
--   3. $C_1\,s_\rho^{-2}\log\frac M{\min\{\beta,\rho\}}\le n^\star(\beta,\rho)\le C_2\,s_\rho^{-2}\log\frac M{\min\{\beta,\rho\}}$.
--
--   The upper bound of Theorem 3.1 is therefore tight up to a constant factor for this family at every chain scale.
--
--   Differences from the source:
--   - encoding: F₂^b, P∗ and P_u, u ≠ 0 → Fin b → ZMod 2; models indexed by u, with u = 0 the uniform law (parityLaw), Γ = parityΓ; reason: Lean indexing; the same experiment
--   - encoding: Θ(s_ρ⁻² log(M/min{β, ρ})) "with universal constants, uniformly in b and ε" → ∃ C₁ C₂ > 0 before b and ε; reason: the Lean reading of Θ
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation
import Definitions.Def_ReplicableDecisions_Supplement_noisyParity

namespace ReplicableDecisions.Supplement

/-- **Theorem 6.2 (The logarithm at every scale).** Chen, *Replicable Decisions in Finite
Experiments*, STOC 2027 submission (sha256 52d181db…), Theorem 6.2, p.27 (PDF p.29). For every
integer `b ≥ 1` and every `0 < ε ≤ 1/2`, the experiment on `F₂^b` consisting of the uniform `P∗`,
forced to answer `0`, and the `2^b − 1` laws `P_u(x) = 2^{−b}(1 + 2εχ_u(x))`, `u ≠ 0`, forced to
answer `1`, has `M = 2^b` models, no indifference models, and `ε²/2 ≤ s_L² ≤ 6ε²/5` for every
`L ≥ 1`. For `0 < β ≤ 1/8` and `0 < ρ ≤ 1/16`, every valid algorithm uses at least
`b log 2/(4ε²)` samples, and
`(1/(45ε²)) log(M/min{β, ρ}) ≤ n⋆(β, ρ) ≤ ⌈(6/ε²) log(M/min{β, ρ})⌉`. In particular
`n⋆(β, ρ) = Θ(s_ρ⁻² log(M/min{β, ρ}))` with universal constants, uniformly in `b` and `ε`.

**Formalization Note.** `noisyParity` and `parityΓ` are the experiment; `M` is the number of models.
The two constants of the `Θ` are quantified before `b` and `ε`. -/
theorem theorem_6_2 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (b : ℕ), 1 ≤ b → ∀ (ε : ℝ) (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2),
        let E := noisyParity b ε hε₀ hε
        let M : ℝ := Fintype.card (Fin b → ZMod 2)
        Fintype.card (Fin b → ZMod 2) = 2 ^ b ∧
        (∀ u : Fin b → ZMod 2, parityΓ u = {false} ∨ parityΓ u = {true}) ∧
        (∀ L : ℕ, 1 ≤ L →
          ε ^ 2 / 2 ≤ hopSeparation E parityΓ L ^ 2 ∧ hopSeparation E parityΓ L ^ 2 ≤ 6 * ε ^ 2 / 5) ∧
        ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
          (∀ n ∈ validSampleSizes E parityΓ β ρ, (b : ℝ) * Real.log 2 / (4 * ε ^ 2) ≤ n) ∧
          ∃ N : ℕ, IsLeast (validSampleSizes E parityΓ β ρ) N ∧
            1 / (45 * ε ^ 2) * Real.log (M / min β ρ) ≤ (N : ℝ) ∧
            N ≤ ⌈6 / ε ^ 2 * Real.log (M / min β ρ)⌉₊ ∧
            C₁ * (1 / hopSeparation E parityΓ (hopBudget ρ) ^ 2 * Real.log (M / min β ρ))
              ≤ (N : ℝ) ∧
            (N : ℝ) ≤
              C₂ * (1 / hopSeparation E parityΓ (hopBudget ρ) ^ 2 * Real.log (M / min β ρ)) := by sorry

end ReplicableDecisions.Supplement
