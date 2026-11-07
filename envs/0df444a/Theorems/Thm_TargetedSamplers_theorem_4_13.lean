-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_13
-- name    : TargetedSamplers.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:29.453798+00:00
-- url     : https://prove2.me/theorems/e6e906ed-097b-49a5-ac8a-2865bc1323b7
-- title:
--   Theorem 4.13 — somewhere-condenser for subconstant-rate inputs
-- statement:
--   There is a universal constant $K$ such that for all constants $\delta,\eta\in(0,1)$ there are a constant $\xi$ with $0<\xi\le K\delta\eta$ and functions
--   $$\mathrm{SCon}_n:\{0,1\}^n\to(\{0,1\}^m)^\ell,\qquad m=\lceil n^{1-\eta}\rceil,\quad \ell\le n^{2\eta},$$
--   such that for every $n\ge1$ and every $\rho\ge n^{-\xi}$, $\mathrm{SCon}_n$ is a $[\rho\mapsto1-\delta]^{1:\ell}_{\sim\gamma}$-somewhere-condenser with $\gamma\le 2^{-c\,n^{1-\eta}}$ for a constant $c>0$, and one program computes $\mathrm{SCon}_n(x)$ (the $\ell$ outputs one after another) in time $O(n^{1+K\eta})$.
--
--   The somewhere-condenser is the first half of the fast condenser of Theorem 4.14.
--
--   Differences from the source:
--   - reading: ξ = O(δη), time O(n^{1+O(η)}) → one universal K with 0 < ξ ≤ Kδη and exponent 1 + Kη; reason: constants of O(·) do not depend on δ, η; ξ = 0 would make the input rate 1
--   - encoding: γ = 2^{−Θ(n^{1−η})} → γ ≤ 2^{−c·n^{1−η}} for some c > 0; reason: being a γ-somewhere-condenser is monotone in γ, so the lower half of Θ adds nothing
--   - encoding: m = n^{1−η} → m = ⌈n^{1−η}⌉; reason: integer output length; Theorem C.1 gives m ∈ [n^{1−η}, n^{1−η+O(δ²)η}]
--   - encoding: every n → every n ≥ 1; reason: at n = 0 the bound ℓ ≤ 0 leaves no output coordinate, an undefined case
--   - reading: "runs in time t" on an unspecified RAM → time at most budget = K·(t+1)·(log₂(n+t+2)+1)^k on the log-cost RAM; reason: the paper fixes no cost model; the log-cost RAM differs from a word RAM by polylogarithmic factors
--   - reading: γ-close: "L1 norm (i.e. statistical distance)" → statistical distance ½‖P−Q‖₁ ≤ γ; reason: the page equates the two; statistical distance is the standard notion for condensers
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.13, p.23 (pdf p.25); Theorem C.1, p.95 (pdf p.97)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSomewhereCondenser
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers

/-- Theorem 4.13 (Somewhere-Condenser for Subconstant-Rate Inputs) (Chen, Doron, Ebtehaj, Tell,
Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, p.23; proof as Theorem C.1,
p.95). For all constants `δ, η ∈ (0,1)` there are a constant `ξ = O(δη)` and a
`[ρ ↦ 1 − δ]^{1:ℓ}_{∼γ}`-somewhere-condenser `SCon : {0,1}ⁿ → ({0,1}^m)^ℓ` for every
`ρ = ρ(n) ≥ n^{−ξ}`, with `m = n^{1−η}`, `ℓ ≤ n^{2η}`, `γ = 2^{−Θ(n^{1−η})}`, computable in time
`O(n^{1+O(η)})`.

**Formalization Note** The constant `K` of `O(δη)` and `O(η)` is universal, chosen before `δ, η`;
`0 < ξ` (with `ξ = 0` the input rate would be 1). `m = ⌈n^{1−η}⌉`. Being a `γ`-condenser is monotone
in `γ`, so `γ = 2^{−Θ(n^{1−η})}` is stated as `γ ≤ 2^{−c·n^{1−η}}` for a constant `c > 0`. The
statement is for `n ≥ 1` (at `n = 0` there are no output coordinates). The program prints the `ℓ`
outputs one after another; time is `budget`. -/
theorem theorem_4_13 : ∃ K : ℝ, 0 < K ∧ ∀ δ η : ℝ, 0 < δ → δ < 1 → 0 < η → η < 1 →
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ K * (δ * η) ∧
    ∃ (m ℓ : ℕ → ℕ) (SCon : (n : ℕ) → (Fin n → Bool) → Fin (ℓ n) → Fin (m n) → Bool) (c : ℝ),
      0 < c ∧
      (∀ n : ℕ, m n = ⌈(n : ℝ) ^ (1 - η)⌉₊) ∧
      (∀ n : ℕ, (ℓ n : ℝ) ≤ (n : ℝ) ^ (2 * η)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ ρ : ℝ, (n : ℝ) ^ (-ξ) ≤ ρ →
        IsSomewhereCondenser ρ (1 - δ) ((2 : ℝ) ^ (-(c * (n : ℝ) ^ (1 - η)))) (SCon n)) ∧
      ∃ (P : Program) (K' k : ℕ), ∀ x : List Bool,
        P.RunsIn (Tapes.ofInput x) (budget K' k ⌈(x.length : ℝ) ^ (1 + K * η)⌉₊ x.length)
          (some ((List.finRange (ℓ x.length)).flatMap fun i =>
            List.ofFn (SCon x.length (toVec x) i))) := by sorry

end TargetedSamplers
