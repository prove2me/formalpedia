-- Prove2me | Theorems.Thm_RobustMultiStop_proposition_4_4
-- name    : RobustMultiStop.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:23.762879+00:00
-- url     : https://prove2.me/theorems/7603b198-21d2-48f9-86fc-b0d1a94d10a3
-- title:
--   Proposition 4.4, (4.13), pp.15–16 — backward recursion of the pathwise maximum $\Theta^q_i$
-- statement:
--   Let $N$ be a horizon, $H$ a reward process and $\bar M^0,\bar M^1,\bar M^2,\dots$ processes with $\bar M^0\equiv0$. For $q\ge0$ and a date $i$ let
--
--   $$\Theta^q_i:=\max_{i\le j_1<j_2<\dots<j_q\le N}\ \sum_{l=1}^{q}\Big(H_{j_l}-\bar M^{q-l+1}_{j_l}+\bar M^{q-l+1}_{j_{l-1}}\Big),\qquad j_0=i,$$
--
--   so that $\Theta^0\equiv0$. Then for $q\ge1$:
--
--   1. if $i+q\le N$,
--   $$\Theta^q_i=\max\Big[H_i+\bar M^{q-1}_i-\bar M^{q-1}_{i+1}+\Theta^{q-1}_{i+1},\ \bar M^q_i-\bar M^q_{i+1}+\Theta^q_{i+1}\Big];\tag{4.13}$$
--   2. if $i+q=N+1$, $\Theta^q_i=H_i+\bar M^{q-1}_i-\bar M^{q-1}_{i+1}+\Theta^{q-1}_{i+1}$.
--
--   The recursion computes the pathwise maximum in the dual (3.3) in $O(LN)$ steps instead of enumerating all tuples, and it is the backbone of the pathwise upper bound in the proof of Theorem 3.1.
--
--   **Formalization Note** The identity holds pointwise for any processes; it uses no property of $\rho$.
--
--   Differences from the source:
--   - encoding: random variables in L⁰(Ω, F, P), (in)equalities P-a.s.; ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P) → a.e.-classes in Ω →ₘ[P] ℝ with their a.s. order; ρ a total map whose values matter at t ≤ N on 𝔛; "∈ L⁰(F_t)" as an F_t-measurable representative; reason: Lean convention; same instances
--   - generalization: f_j(X_j) and the regression martingales M̄^q of the algorithm, 0 ≤ i ≤ T, Θ^q_i = 0 for i > T and Θ^q_T = f_T(X_T) → any processes H and M̄^q; dates on a horizon N, (4.13) for i + q ≤ N and its first branch alone at i + q = N + 1; reason: the identity is pathwise lattice algebra; with N = T + L, H_j = 0 and M̄ constant after T, Θ^q_i for i ≤ T is the paper's Θ^q_i (Θ^q_{T+1} = 0), and every i ≤ T, q ≤ L has i + q ≤ N
--   - reading: M̄^{q−1} at q = 1 is not defined → M̄⁰ ≡ 0; reason: the only reading compatible with the initialization Θ⁰ = 0 at q = 1
--   - encoding: legs l = 1, …, q carry M̄^{q−l+1} → 0-based legs l carry Mbar (q − l); reason: index shift only
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, Proposition 4.4 and (4.13), pp.15–16; "Initialize Θ⁰_i = 0", p.16

import Mathlib
import Definitions.Def_RobustMultiStop_dualMax

open MeasureTheory

namespace RobustMultiStop

/-- Proposition 4.4, (4.13), Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping —
A Pathwise Duality Approach*, arXiv:2006.01802v2, pp.15–16: "Define, for `1 ≤ q ≤ L` and
`0 ≤ i ≤ T`, `Θ^q_i := max_{i≤j_1<j_2<⋯<j_q} Σ_{l=1}^q (f_{j_l}(X_{j_l}) − M̄^{q−l+1}_{j_l} +
M̄^{q−l+1}_{j_{l−1}})`, with `j_0 = i`, and naturally `Θ^q_i = 0`, `i > T`. Then,
`Θ^q_i = max[f_i(X_i) + M̄^{q−1}_i − M̄^{q−1}_{i+1} + Θ^{q−1}_{i+1}, M̄^q_i − M̄^q_{i+1} + Θ^q_{i+1}]`. (4.13)"

Here `Θ^q_i` is `dualMax N H i (fun l : Fin q => Mbar (q - l))` (the leg `l`, `0`-based, carries
`M̄^{q−l}`), `Θ⁰ = 0` ("Initialize `Θ⁰_i = 0`", p.16) and `M̄⁰ = 0`. (4.13) holds when both branches
have a tuple (`i + q ≤ N`); when `i + q = N + 1` only the first branch has one, and `Θ^q_i` equals it.

**Formalization Note** The reward `f_j(X_j)` is any process `H`, and `M̄` is any family of
processes: the identity is pure lattice algebra in `Ω →ₘ[P] ℝ`. `N` is the horizon (the paper's
`T`). `M̄⁰ = 0` is the only reading of `M̄^{q−1}` at `q = 1` compatible with `Θ⁰ = 0`. -/
theorem proposition_4_4 {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (N : ℕ) (H : ℕ → Ω →ₘ[P] ℝ) (Mbar : ℕ → ℕ → Ω →ₘ[P] ℝ) (hM0 : ∀ i, Mbar 0 i = 0)
    (q i : ℕ) (hq : 1 ≤ q) :
    (i + q ≤ N →
      dualMax N H i (fun l : Fin q => Mbar (q - (l : ℕ))) =
        (H i + Mbar (q - 1) i - Mbar (q - 1) (i + 1) +
            dualMax N H (i + 1) (fun l : Fin (q - 1) => Mbar (q - 1 - (l : ℕ)))) ⊔
          (Mbar q i - Mbar q (i + 1) + dualMax N H (i + 1) (fun l : Fin q => Mbar (q - (l : ℕ))))) ∧
    (i + q = N + 1 →
      dualMax N H i (fun l : Fin q => Mbar (q - (l : ℕ))) =
        H i + Mbar (q - 1) i - Mbar (q - 1) (i + 1) +
          dualMax N H (i + 1) (fun l : Fin (q - 1) => Mbar (q - 1 - (l : ℕ)))) := by sorry

end RobustMultiStop
