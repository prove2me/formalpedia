-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_theorem_6_1
-- name    : RandProdExp.TwoSided.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:19:37.849197+00:00
-- url     : https://prove2.me/theorems/beb43d42-5b6f-432d-9bd2-3c5718f4f7fc
-- title:
--   Theorem 6.1 — one prime $p=O_D(2^{n^D}n^D\log n)$: for every $t\ge1$ all $\tau_M$ injective for $(C_i)$ and $(C_i^\perp)$ with probability $\ge1-p^{1-t}/\log(n+1)$
-- statement:
--   For every $D\ge1$ there is a constant $C_D>0$ such that the following holds. Let $0<\rho<1/2$, $0<\varepsilon\le\varepsilon_0(D,\rho)$, $n\ge N^*_{D,\varepsilon}$ (Equation (16)) and let $k_1,\dots,k_D$ be integers with $\rho n\le k_i\le(1-\rho)n$. Then there is a prime $p\le C_D\,2^{n^D}n^D\log n$ such that for every integer $t\ge1$, if $C_i\in\mathrm{Gr}_{p^t}(n,k_i)$ are independent and uniformly random, then
--   $$\Pr\Big[\tau_M\text{ is injective for every }\varepsilon\text{-closed }M\subseteq[n]^D,\ \text{for }(C_i)_{i\in[D]}\text{ and for }(C_i^\perp)_{i\in[D]}\Big]\ \ge\ 1-\frac{p^{1-t}}{\log(n+1)} .$$
--   The prime is chosen before $t$ and before the codes. By Lemma 4.5 and Lemma 5.2 this gives the goal at $t=1$.
--
--   Differences from the source:
--   - encoding: p = O_D(2^{n^D} n^D log n) → ∃ C_D > 0 (depending on D only, chosen before ρ, ε, n, k), p ≤ C_D · 2^{n^D} · n^D · Real.log n; reason: O_D is a constant depending only on D (Theorem 1, p. 4)
--   - encoding: C_i ∼ Gr_{p^t}(n, k_i) independently; F_{p^t} → uniform counting probability on ∏_i Gr(n, k_i) over GaloisField p t (codeProb); reason: independent uniform choices on finite sets
--   - encoding: n ≥ N*_{D,ε}, log natural → (N*_{D,ε} : ℝ) ≤ n with N* the integer ceiling; Real.log; reason: same condition for integer n; the paper's log is natural (Theorem 3.25, p. 67)
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 35, Theorem 6.1 (proved pp. 43–45)

import Mathlib
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Codes
import Definitions.Def_RandProdExp_TwoSided_Params

namespace RandProdExp.TwoSided

/-- **Theorem 6.1** (p. 35). For every `D ≥ 1` there is a constant `C_D > 0` such that for all
`0 < ρ < 1/2`, `0 < ε ≤ ε₀(D, ρ)`, `n ≥ N*_{D,ε}` and integers `ρ n ≤ k_i ≤ (1 − ρ) n`, there is a prime
`p ≤ C_D 2^{n^D} n^D log n` such that for every integer `t ≥ 1`, if `C_i ∈ Gr_{p^t}(n, k_i)` are
independent and uniform, then with probability at least `1 − p^{1−t} / log(n + 1)` the corestriction
map `τ_M` is injective for every ε-closed `M ⊆ [n]^D`, simultaneously for `(C_i)` and `(C_i^⊥)`. -/
theorem theorem_6_1 (D : ℕ) (hD : 1 ≤ D) :
    ∃ CD : ℝ, 0 < CD ∧
      ∀ (ρ ε : ℝ), 0 < ρ → ρ < 1 / 2 → 0 < ε → ε ≤ eps0 D ρ →
      ∀ n : ℕ, (Nstar D ε : ℝ) ≤ n →
      ∀ k : Fin D → ℕ, (∀ i, ρ * n ≤ k i ∧ (k i : ℝ) ≤ (1 - ρ) * n) →
      ∃ (p : ℕ) (_ : Fact p.Prime),
        (p : ℝ) ≤ CD * 2 ^ (n ^ D) * (n : ℝ) ^ D * Real.log n ∧
        ∀ t : ℕ, 1 ≤ t →
          1 - (p : ℝ) ^ (1 - (t : ℤ)) / Real.log (n + 1) ≤
            codeProb (GaloisField p t) n k (fun C =>
              ∀ M : Set (Fin D → Fin n), IsEpsClosed ε M →
                Function.Injective (tauMap M (fun i => (C i).1)) ∧
                Function.Injective (tauMap M (fun i => GoodQLTC.dualCode (C i).1))) := by sorry

end RandProdExp.TwoSided
