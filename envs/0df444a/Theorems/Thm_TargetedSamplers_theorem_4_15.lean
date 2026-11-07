-- Prove2me | Theorems.Thm_TargetedSamplers_theorem_4_15
-- name    : TargetedSamplers.theorem_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:07:46.095483+00:00
-- url     : https://prove2.me/theorems/0f518d5e-45ba-4fd3-a41a-6aab49dead77
-- title:
--   Theorem 4.15 — error reduction by a condenser
-- statement:
--   Let $\alpha,\beta>0$. There is $N_0$ such that for every $T_b\ge N_0$, every $T_a,d$, every $B:\{0,1\}^{T_b}\to\{0,1\}$ and $\sigma\in\{0,1\}$ with $|B^{-1}(\sigma)|\le 2^{(1-\beta)T_b}$, and every $[T_a^{-\alpha}\mapsto1-\beta/2]_{\sim1/6}$-condenser $\mathrm{Con}:\{0,1\}^{T_a}\times\{0,1\}^d\to\{0,1\}^{T_b}$, the function
--   $$A(z)=\mathrm{MAJ}_{s\in\{0,1\}^d}\{B(\mathrm{Con}(z,s))\}$$
--   satisfies $|A^{-1}(\sigma)|\le 2^{T_a^{1-\alpha}}$.
--
--   Applied to an algorithm $B$ with few bad coin strings, this reduces the number of bad coin strings at the cost of enumerating the $2^d$ seeds.
--
--   Differences from the source:
--   - reading: "let T_b be sufficiently large" → T_b ≥ N₀ with N₀ depending only on α, β; reason: the threshold of the proof (2^{−βT_b/2} + 1/3 ≤ 1/2) depends only on β
--   - encoding: MAJ over the 2^d seeds → 1 iff more than half of the seeds give 1 (a tie gives 0); reason: the page does not fix a tie rule; the proof works for either
--   - reading: γ-close: "L1 norm (i.e. statistical distance)" → statistical distance ½‖P−Q‖₁ ≤ γ; reason: the page equates the two; statistical distance is the standard notion for condensers
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.15, p.24 (pdf p.26)

import Mathlib
import Definitions.Def_TargetedSamplers_IsCondenser

namespace TargetedSamplers

/-- Theorem 4.15 (Error Reduction by Condenser) (Chen, Doron, Ebtehaj, Tell, Targeted Samplers,
STOC 2027 submission, manuscript sha256 599d0a59…, p.24). Let `α, β > 0` and let `T_b` be
sufficiently large. Let `B : {0,1}^{T_b} → {0,1}` with `|B^{−1}(σ)| ≤ 2^{(1−β)T_b}` for some
`σ ∈ {0,1}`, and let `Con : {0,1}^{T_a} × {0,1}^d → {0,1}^{T_b}` be a
`[T_a^{−α} ↦ 1 − β/2]_{∼1/6}`-condenser. Then `A(z) = MAJ_{s ∈ {0,1}^d} B(Con(z, s))` satisfies
`|A^{−1}(σ)| ≤ 2^{T_a^{1−α}}`.

**Formalization Note** "Sufficiently large" is a threshold `N₀` depending on `α, β` only.
`MAJ` outputs `1` iff more than half of the `2^d` seeds give `1` (a tie gives `0`); the proof works for
either tie rule. -/
theorem theorem_4_15 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ N₀ : ℕ, ∀ Tb : ℕ, N₀ ≤ Tb → ∀ (Ta d : ℕ) (B : (Fin Tb → Bool) → Bool) (σ : Bool),
      ((Finset.univ.filter (fun y => B y = σ)).card : ℝ) ≤ (2 : ℝ) ^ ((1 - β) * Tb) →
      ∀ Con : (Fin Ta → Bool) → (Fin d → Bool) → (Fin Tb → Bool),
        IsCondenser ((Ta : ℝ) ^ (-α)) (1 - β / 2) (1 / 6) Con →
        ((Finset.univ.filter (fun z =>
            decide (2 * (Finset.univ.filter (fun s => B (Con z s) = true)).card > 2 ^ d) = σ)).card
          : ℝ) ≤ (2 : ℝ) ^ ((Ta : ℝ) ^ (1 - α)) := by sorry

end TargetedSamplers
