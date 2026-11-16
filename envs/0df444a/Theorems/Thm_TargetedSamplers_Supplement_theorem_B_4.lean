-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_B_4
-- name    : TargetedSamplers.Supplement.theorem_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:17:55.870608+00:00
-- url     : https://prove2.me/theorems/60591293-e07b-49e4-9b3d-3f27e1325546
-- title:
--   Theorem B.4 — the basic somewhere-condenser
-- statement:
--   For every constant $\delta\in(0,1)$ there are $\epsilon=O(\delta)$, the integer $\ell=3\lceil(1+\epsilon)/\epsilon\rceil$ and a family $\mathrm{bSCon}_n:\{0,1\}^n\to(\{0,1\}^m)^\ell$, computable in time $\widetilde O(n)$, such that for every sufficiently large $n$ and every $\rho=\rho(n)\in[0,1]$, $\mathrm{bSCon}_n$ is a $[\rho\mapsto\rho']^{1:\ell}_{\sim\gamma}$-somewhere-condenser, where
--   $$m=\Big\lceil\frac{n}{\ell-1}\Big\rceil,\qquad\rho'=\min\{\rho(1+\epsilon^2/8),\,1-2\delta\},\qquad\gamma=2^{-\Theta(\rho m)}.$$
--
--   Iterating this map raises the min-entropy rate by the constant factor $1+\epsilon^2/8$ per step while multiplying the number of output blocks by $\ell$; Theorem B.7 does so.
--
--   **Formalization Note** $\epsilon=O(\delta)$ is $0<\epsilon\le K\delta$ with a universal $K$; $\gamma=2^{-\Theta(\rho m)}$ is $\gamma\le2^{-c\rho m}$ with $c>0$ depending only on $\delta$ (being a somewhere-condenser is monotone in $\gamma$). Somewhere-condensers are the base mission's `IsSomewhereCondenser`; the program prints the $\ell$ blocks one after another.
--
--   Differences from the source:
--   - encoding: ϵ = O(δ) → 0 < ϵ ≤ K·δ with K universal, chosen before δ; reason: ϵ must be positive for ℓ to be defined
--   - encoding: γ = 2^{−Θ(ρm)} → γ ≤ 2^{−c·ρ·m} with c > 0 depending only on δ; reason: being a γ-somewhere-condenser is monotone in γ, as in base Theorem 4.13
--   - encoding: every sufficiently large n and every ρ = ρ(n) ∈ [0, 1] → ∃ n₀ (depending on δ) ∀ n ≥ n₀ ∀ ρ ∈ [0, 1]; reason: a function ρ(n) is a choice of ρ for each n
--   - encoding: computable in time Õ(n) → one program printing the ℓ output blocks within budget(n); reason: the base mission's convention
--   - encoding: outputs ({0,1}^m)^ℓ → blocks indexed by Fin ℓ; reason: a relabelling
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem B.4, p.90 (pdf p.92)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSomewhereCondenser
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers.Supplement

/-- Theorem B.4 (the basic somewhere-condenser) (Chen, Doron, Ebtehaj, Tell, Targeted Samplers,
STOC 2027 submission, manuscript sha256 599d0a59…, p.90). For any constant `δ ∈ (0, 1)` there are
`ϵ = O(δ)`, the integer `ℓ = 3⌈(1 + ϵ)/ϵ⌉` and a family `bSCon_n : {0,1}ⁿ → ({0,1}^m)^ℓ`, computable in
time `Õ(n)`, such that for every sufficiently large `n` and every `ρ = ρ(n) ∈ [0, 1]`, `bSCon_n` is a
`[ρ ↦ ρ′]^{1:ℓ}_{∼γ}`-somewhere-condenser with `m = ⌈n/(ℓ − 1)⌉`,
`ρ′ = min{ρ · (1 + ϵ²/8), 1 − 2δ}` and `γ = 2^{−Θ(ρm)}`.

**Formalization Note** `ϵ = O(δ)` is `0 < ϵ ≤ K · δ` with a universal constant `K` chosen before
`δ`. Being a `γ`-somewhere-condenser is monotone in `γ`, so `γ = 2^{−Θ(ρm)}` is stated as
`γ ≤ 2^{−c·ρ·m}` with a constant `c > 0` depending only on `δ` (as in base Theorem 4.13). "Every
sufficiently large `n`" is `n ≥ n₀` with `n₀` depending on `δ`; the statement holds for every
`ρ ∈ [0, 1]` at once. The `ℓ` output blocks are indexed by `Fin ℓ`; the program prints them one after
another, and `Õ(n)` is `budget` with `t = n`. -/
theorem theorem_B_4 : ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ϵ : ℝ, 0 < ϵ ∧ ϵ ≤ K * δ ∧
    ∃ (ℓ : ℕ) (m : ℕ → ℕ) (bSCon : (n : ℕ) → (Fin n → Bool) → Fin ℓ → Fin (m n) → Bool) (c : ℝ),
      ℓ = 3 * ⌈(1 + ϵ) / ϵ⌉₊ ∧ 0 < c ∧
      (∀ n : ℕ, m n = ⌈(n : ℝ) / ((ℓ : ℝ) - 1)⌉₊) ∧
      (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        IsSomewhereCondenser ρ (min (ρ * (1 + ϵ ^ 2 / 8)) (1 - 2 * δ))
          ((2 : ℝ) ^ (-(c * ρ * (m n : ℝ)))) (bSCon n)) ∧
      ∃ (P : Program) (K' k : ℕ), ∀ x : List Bool,
        P.RunsIn (Tapes.ofInput x) (budget K' k x.length x.length)
          (some ((List.finRange ℓ).flatMap fun i =>
            List.ofFn (bSCon x.length (toVec x) i))) := by sorry

end TargetedSamplers.Supplement
