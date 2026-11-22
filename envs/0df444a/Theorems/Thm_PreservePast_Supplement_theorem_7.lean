-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_7
-- name    : PreservePast.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:34:57.60806+00:00
-- url     : https://prove2.me/theorems/3f29eb92-e30e-4cd9-a43d-d34e49327b33
-- title:
--   Theorem 7 — individual versus average protection
-- statement:
--   Consider histories of $K$ regression tasks with $\mathbb E_i\|X\|^2\le 2$ and $\mathbb E_i\|W_0X-Y\|^2\le 1$, at radius $R=\sqrt2$, accuracy $\epsilon=201/20000$, fit tolerance $\xi=1/20000$ and failure probability $\beta=1/3$. There is an absolute $\gamma>0$ such that, for all sufficiently large $n$, all $1\le r\le m\le n$ and all $1\le K\le\exp(\gamma n)$,
--   $$B_{\mathrm{individual}}=\Theta(Kn),\qquad B_{\mathrm{average}}=\Theta(n).$$
--   The constants do not depend on $K,n,m,r$. The upper bounds are deterministic; the lower bounds allow arbitrary joint randomized messages.
--
--   Protecting each old task separately forbids cross-task compensation and costs a factor $K$ more memory than protecting their average.
--
--   **Formalization Note** Individual protection is the published contract (`PreservePast.RandAchieves`, `PreservePast.DetAchieves`) for a $K$-tuple of tasks; average protection is `RandAchievesAvg`, `DetAchievesAvg`. The statement holds for every public checkpoint $W_0$.
--
--   Differences from the source:
--   - encoding: B = Θ(·) with constants independent of K, n, m, r, for all sufficiently large n → absolute γ, c, C > 0 and N₀ chosen first; for n ≥ N₀, c·X ≤ B for every randomized achieving width and a deterministic code of width B ≤ C·X; reason: spells out Θ and "sufficiently large", and avoids the junk value of an infimum over an empty set
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 7, p.9 (PDF p.11), eq. (20)

import Mathlib
import Definitions.Def_PreservePast_RandAchieves
import Definitions.Def_PreservePast_DetAchieves
import Definitions.Def_PreservePast_Supplement_RandAchievesAvg

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 7 (Individual versus average protection).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 7, p.9 (PDF p.11), eq. (20).

There are absolute `γ, c, C > 0` and `N₀` such that for all `n ≥ N₀`, `1 ≤ r ≤ m ≤ n`,
`1 ≤ K ≤ exp(γ n)` and every public checkpoint `W₀`, at `R = √2`, `ε = 201/20000`,
`ξ = 1/20000`, `β = 1/3`: every randomized protocol protecting each of the `K` tasks
individually uses `B ≥ c K n` bits and a deterministic code does so with `B ≤ C K n` bits; every
randomized protocol protecting the average uses `B ≥ c n` bits and a deterministic code does so
with `B ≤ C n` bits.

**Formalization Note.** `B = Θ(·)` is stated in the two-part form of the published goal
(a lower bound for every achieving width and an achieving code for the upper bound), which
avoids `sInf ∅`. "For all sufficiently large n" is `∃ N₀, ∀ n ≥ N₀`; the constants `γ, c, C, N₀`
are chosen before `K, n, m, r, W₀` ("The constants do not depend on K, n, m, r"). Individual
protection is the published contract `RandAchieves`/`DetAchieves` with a `K`-tuple history
(`max_i f_i(H) ≤ ε`); the tasks satisfy `𝔼_i‖X‖² ≤ 2`, `𝔼_i‖W₀X − Y‖² ≤ 1` by the definition of
`Task`. Coin spaces live in `Type`. -/
theorem theorem_7 :
    ∃ γ : ℝ, 0 < γ ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
      ∀ (m n r K : ℕ) (W₀ : Matrix (Fin m) (Fin n) ℝ),
        N₀ ≤ n → 1 ≤ r → r ≤ m → m ≤ n → 1 ≤ K → (K : ℝ) ≤ Real.exp (γ * n) →
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (enc : (Fin K → Task W₀) → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
            RandAchieves P enc dec r (201 / 20000) (1 / 20000) (Real.sqrt 2) (1 / 3) →
              c * K * n ≤ (B : ℝ)) ∧
        (∃ B : ℕ, (B : ℝ) ≤ C * K * n ∧
          ∃ (enc : (Fin K → Task W₀) → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
            DetAchieves enc dec r (201 / 20000) (1 / 20000) (Real.sqrt 2)) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (enc : (Fin K → Task W₀) → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
            RandAchievesAvg P enc dec r (201 / 20000) (1 / 20000) (Real.sqrt 2) (1 / 3) →
              c * n ≤ (B : ℝ)) ∧
        ∃ B : ℕ, (B : ℝ) ≤ C * n ∧
          ∃ (enc : (Fin K → Task W₀) → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
            DetAchievesAvg enc dec r (201 / 20000) (1 / 20000) (Real.sqrt 2) := by sorry

end PreservePast.Supplement
