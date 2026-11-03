-- Prove2me | Theorems.Thm_ProxFlatIP_eq_8
-- name    : ProxFlatIP.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:40.691406+00:00
-- url     : https://prove2.me/theorems/16d4ea74-1f15-45c0-9946-eb2ffd93d88f
-- title:
--   Display (8) (corrected: $\max_P\alpha^\top x\le\kappa_d\Delta^\alpha$) — $\kappa_d(\alpha)<\frac{4n+2}{9}$, so $\alpha^\top x<\frac{4n+2}{9}\Delta^\alpha(A)$ on $P$ when $P\cap\mathbb Z^n=\{0\}$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $n\ge2$, $b\in\mathbb Z^m$, and let $\alpha\in\mathbb Z^n$ be nonzero. Suppose $P(A,b)\cap\mathbb Z^n=\{0\}$, and let $d=\dim P(A,b)$. Then
--   $$\alpha^\top x\le\kappa_d(\alpha)\cdot\Delta^\alpha(A)\ \text{ for every }x\in P(A,b),\qquad \kappa_d(\alpha)<\frac{4n+2}{9},$$
--   and hence, for every $x\in P(A,b)$,
--   $$\alpha^\top x<\frac{4n+2}{9}\cdot\Delta^\alpha(A).$$
--
--   This is the bound on a single linear form from which the proximity theorems follow, after translating the instance so that the optimal integer solution is the origin.
--
--   Differences from the source:
--   - correction: max_{x∈P} α⊤x = κ_d(α)·Δ^α(A) → α⊤x ≤ κ_d(α)·Δ^α(A) for every x ∈ P; reason: the equality fails when dim P < n: A with rows (0,1), (0,−1), (2,1), (−2,1), (1,3), b = (0,0,1,1,5), α = e₁ satisfy every assumption, P = [−1/2,1/2] × {0}, max α⊤x = 1/2 and Δ^α(A) = 3, but I = {1} has dim P_I = 1 and κ_I(α) = 1/2, so κ_1(α)·Δ^α(A) ≥ 3/2; the equality holds when dim P = n
--   - encoding: max_{x∈P} α⊤x < (4n+2)/9·Δ^α(A) → α⊤x < (4n+2)/9·Δ^α(A) for every x ∈ P; reason: P ∩ Zⁿ = {0} makes P bounded, so the maximum is attained and the two bounds are the same
--   - encoding: κ_I is the number with max_{x∈P_I} α⊤x = κ_I·Δ^α_I(A), with no value when Δ^α_I(A) = 0 → κ_I = 0 there (Lean's x/0 = 0); reason: Δ^α_I(A) = 0 only when α lies in the row space of A_I, so α⊤x = 0 on P_I and (2) holds for every κ_I; no instance with Δ^α_I(A) > 0 changes
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, (8), p.10, in the proof of Theorem 5

import Mathlib
import Definitions.Def_ProxFlatIP_Kappa

open Matrix

namespace ProxFlatIP

/-- **Display (8)** (corrected: `max α⊤x = κ_d Δ^α` read as `≤`) (arXiv:2211.14941v1, (8), p.10, in
the proof of Theorem 5). Let `n ≥ 2`, `α ∈ ℤⁿ` be nonzero, `P ∩ ℤⁿ = {0}`, and `d = dim P`. Then
`α⊤x ≤ κ_d(α) Δ^α(A)` for every `x ∈ P`, `κ_d(α) < (4n+2)/9`, and `α⊤x < ((4n+2)/9) Δ^α(A)` for every
`x ∈ P`.

**Formalization Note.** The display reads `max_{x∈P} α⊤x = κ_d(α) Δ^α(A) < ((4n+2)/9) Δ^α(A)`, after
the chain `κ_d(α) ≤ … ≤ (4n+2)/9` with one strict step. The maximum exists here (`P ∩ ℤⁿ = {0}` makes
`P` bounded), so it is stated on every point. The printed `=` holds when `dim P = n` but is only `≤`
in general: for `A` with rows `(0,1), (0,−1), (2,1), (−2,1), (1,3)`, `b = (0,0,1,1,5)` and `α = e₁`,
`P = [−½,½] × {0}`, `max α⊤x = ½`, `Δ^α(A) = 3`, and `I = {1}` gives `κ_1(α) ≥ ½`. `κ_d` uses the
conventions of `kappaD` (`sSup ∅ = 0`, `x / 0 = 0`). -/
theorem eq_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (hn : 2 ≤ n)
    (b : Fin m → ℤ) (α : Fin n → ℤ) (hα : α ≠ 0) (hP : Poly A b ∩ {x | IsIntegralPt x} = {0}) :
    (∀ x ∈ Poly A b,
        castVec α ⬝ᵥ x ≤ kappaD A b α (dimLin (Poly A b)) * (deltaAlpha A α : ℝ)) ∧
      kappaD A b α (dimLin (Poly A b)) < (4 * (n : ℝ) + 2) / 9 ∧
      ∀ x ∈ Poly A b, castVec α ⬝ᵥ x < (4 * (n : ℝ) + 2) / 9 * (deltaAlpha A α : ℝ) := by sorry

end ProxFlatIP
