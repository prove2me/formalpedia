-- Prove2me | Theorems.Thm_PreservePast_lower_bound
-- name    : PreservePast.lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:42:46.213881+00:00
-- url     : https://prove2.me/theorems/ff11c02c-9479-4c21-89b8-de1567929a64
-- title:
--   §C.6 — the lower bound $B\ge c_\beta(F_C+F_R)$, for every $\sqrt2\le R\le\sqrt3$
-- statement:
--   Assume one old task ($K=1$), exact fit ($\xi=0$), $0<\beta<1/2$, $n\ge N_\beta$ (71), $1\le r\le m\le n$ and $0<\epsilon\le2^{-28}$, and let $\sqrt2\le R\le\sqrt3$. Then there is $c_\beta>0$, depending only on $\beta$, such that for every checkpoint $W_0$, every randomized $B$-bit protocol (joint randomized messages allowed) that returns a successful update with probability at least $1-\beta$ for each fixed history and each promised query has
--   $$
--   B\ \ge\ c_\beta\,(F_C+F_R).
--   $$
--
--   This is the lower half of Theorem 4.
--
--   **Formalization Note** $c_\beta$ is chosen after $\beta$ and before $m,n,r,\epsilon,R,W_0$, so it is uniform in $m/r$. The coin space of the protocol is an arbitrary type; the bound is stated for every achieving width, so `sInf ∅ = 0` plays no role.
--
--   Differences from the source:
--   - generalization: radius R = √3 (Theorem 4) → every √2 ≤ R ≤ √3; reason: the paper proves the lower bound 'in fact for every √2 ≤ R ≤ √3' (p.24); R = √3 is one instance
--   - encoding: B_full ≥ … with B_full the least register size → every width B of a protocol achieving the task satisfies the bound; reason: equivalent to the B_full bound, without the junk value sInf ∅ = 0
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.6, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_PreservePast_RandAchieves
import Definitions.Def_PreservePast_FC

open MeasureTheory

namespace PreservePast

universe u

/-- **The lower bound of (16), §C.6.** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.6, p.24 (PDF p.26): "We prove
B_full ≥ c_β(F_C + F_R) under the theorem's assumptions, in fact for every √2 ≤ R ≤ √3. The
constant is uniform in m/r, and the argument permits arbitrary joint randomized messages with
success for each fixed history and promised query."

Under Theorem 4's assumptions (`K = 1`, `ξ = 0`, `n ≥ N_β` from (71), `1 ≤ r ≤ m ≤ n`,
`0 < ϵ ≤ 2^{−28}`), for every radius `√2 ≤ R ≤ √3` and every checkpoint `W₀`: every width `B` of a
randomized protocol (arbitrary coin space, joint randomized messages) that succeeds with
probability at least `1 − β` for each fixed history and each promised query satisfies
`B ≥ c_β(F_C + F_R)`.

**Formalization Note.** `c` depends only on `β` (chosen before `m, n, r, ϵ, R, W₀`; in particular
uniform in `m/r`). The coin space is an arbitrary type in any universe. The bound `B_full ≥ c_β(F_C + F_R)` is stated for every achieving width,
so that `sInf ∅ = 0` plays no role. -/
theorem lower_bound :
    ∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      ∀ (m n r : ℕ) (ε R : ℝ) (W₀ : Matrix (Fin m) (Fin n) ℝ),
        Nbeta β ≤ n → 1 ≤ r → r ≤ m → m ≤ n → 0 < ε → ε ≤ (2 : ℝ) ^ (-28 : ℤ) →
        Real.sqrt 2 ≤ R → R ≤ Real.sqrt 3 →
        ∀ (B : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
          (enc : (Fin 1 → Task W₀) → Ω → Fin (2 ^ B))
          (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
          RandAchieves P enc dec r ε 0 R β → c * (FC n ε + FR n r ε) ≤ (B : ℝ) := by sorry

end PreservePast
