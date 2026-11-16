-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_B_7
-- name    : TargetedSamplers.Supplement.theorem_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:18:43.606202+00:00
-- url     : https://prove2.me/theorems/0bd3f26b-8fbb-4ecb-b681-24dd4a8da60e
-- title:
--   Theorem B.7 — a somewhere-condenser from rate $n^{-\xi}$ to rate $1-2\delta$ (another version of Theorem 4.13)
-- statement:
--   For every pair of constants $\delta,\eta\in(0,1)$ there is $\xi=O(\eta\delta^3)$ and a function $\mathrm{SCon}_n:\{0,1\}^n\to(\{0,1\}^m)^\ell$, computable in time $n^{1+O(\delta\eta)}$, that is an $[n^{-\xi}\mapsto1-2\delta]^{1:\ell}_{\sim\gamma}$-somewhere-condenser, where
--   $$m=n^{1-\eta},\qquad\ell\le n^{(1+O(\delta))\eta},\qquad\gamma=2^{-\Theta(n^{1-\eta})}.$$
--
--   Compared with Theorem 4.13 of the base mission, the output rate is $1-2\delta$ instead of $1-\delta$, the number of blocks is $n^{(1+O(\delta))\eta}$ instead of $n^{2\eta}$, and the running time is $n^{1+O(\delta\eta)}$; neither statement implies the other.
--
--   **Formalization Note** As in base Theorem 4.13: one universal constant $K$ for $O(\eta\delta^3)$, $O(\delta)$ and $O(\delta\eta)$; $m=\lceil n^{1-\eta}\rceil$; $\gamma\le2^{-cn^{1-\eta}}$ with $c>0$; every $n\ge1$; the program prints the $\ell$ blocks one after another.
--
--   Differences from the source:
--   - encoding: ξ = O(η·δ³); ℓ ≤ n^{(1+O(δ))η}; time n^{1+O(δη)} → 0 < ξ ≤ K·η·δ³, ℓ ≤ n^{(1+Kδ)η}, time budget(⌈n^{1+Kδη}⌉) with K universal, chosen before δ, η; reason: as in base Theorem 4.13; ξ = 0 would make the input rate 1
--   - encoding: m = n^{1−η} → m = ⌈n^{1−η}⌉; reason: a length is an integer; base Theorem 4.13's convention
--   - encoding: γ = 2^{−Θ(n^{1−η})} → γ ≤ 2^{−c·n^{1−η}} with c > 0; reason: being a γ-somewhere-condenser is monotone in γ
--   - encoding: SCon_n for every n → every n ≥ 1; reason: at n = 0 there is no source of positive rate; base Theorem 4.13's convention
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem B.7, p.93 (pdf p.95)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSomewhereCondenser
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers.Supplement

/-- Theorem B.7 (another version of Theorem 4.13) (Chen, Doron, Ebtehaj, Tell, Targeted Samplers,
STOC 2027 submission, manuscript sha256 599d0a59…, p.93). For any constants `δ, η ∈ (0, 1)` there is
`ξ = O(η · δ³)` such that some `SCon_n : {0,1}ⁿ → ({0,1}^m)^ℓ`, computable in time `n^{1+O(δη)}`, is
an `[n^{−ξ} ↦ 1 − 2δ]^{1:ℓ}_{∼γ}`-somewhere-condenser, where `m = n^{1−η}`, `ℓ ≤ n^{(1+O(δ))η}` and
`γ = 2^{−Θ(n^{1−η})}`.

**Formalization Note** As in base Theorem 4.13: the constant `K` of `O(η · δ³)`, `O(δ)` and `O(δη)`
is universal, chosen before `δ, η`; `0 < ξ` (with `ξ = 0` the input rate would be `1`).
`m = ⌈n^{1−η}⌉`. Being a `γ`-somewhere-condenser is monotone in `γ`, so `γ = 2^{−Θ(n^{1−η})}` is
stated as `γ ≤ 2^{−c·n^{1−η}}` for a constant `c > 0`. The statement is for every `n ≥ 1` (at `n = 0`
there is no source of positive rate). The input rate is exactly `n^{−ξ}`; a source of larger rate is
also an `(n, n^{−ξ} n)`-source. The program prints the `ℓ` outputs one after another; time is
`budget`. -/
theorem theorem_B_7 : ∃ K : ℝ, 0 < K ∧ ∀ δ η : ℝ, 0 < δ → δ < 1 → 0 < η → η < 1 →
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ K * (η * δ ^ 3) ∧
    ∃ (m ℓ : ℕ → ℕ) (SCon : (n : ℕ) → (Fin n → Bool) → Fin (ℓ n) → Fin (m n) → Bool) (c : ℝ),
      0 < c ∧
      (∀ n : ℕ, m n = ⌈(n : ℝ) ^ (1 - η)⌉₊) ∧
      (∀ n : ℕ, (ℓ n : ℝ) ≤ (n : ℝ) ^ ((1 + K * δ) * η)) ∧
      (∀ n : ℕ, 1 ≤ n →
        IsSomewhereCondenser ((n : ℝ) ^ (-ξ)) (1 - 2 * δ)
          ((2 : ℝ) ^ (-(c * (n : ℝ) ^ (1 - η)))) (SCon n)) ∧
      ∃ (P : Program) (K' k : ℕ), ∀ x : List Bool,
        P.RunsIn (Tapes.ofInput x) (budget K' k ⌈(x.length : ℝ) ^ (1 + K * (δ * η))⌉₊ x.length)
          (some ((List.finRange (ℓ x.length)).flatMap fun i =>
            List.ofFn (SCon x.length (toVec x) i))) := by sorry

end TargetedSamplers.Supplement
