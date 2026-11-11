-- Prove2me | Theorems.Thm_PreservePast_theorem_4
-- name    : PreservePast.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:42:52.240683+00:00
-- url     : https://prove2.me/theorems/d9d31165-a338-497c-9fea-a5bd6ca033a4
-- title:
--   Theorem 4 — the complete regression class at general rank: $c_\beta(F_C+F_R)\le B_{\mathrm{full}}\le C\mathcal L^3(F_C+F_R)$
-- statement:
--   Fix a public checkpoint $W_0\in\mathbb R^{m\times n}$ and one old task $(X,Y)$ with $\mathbb E\|X\|^2\le2$ and $\mathbb E\|W_0X-Y\|^2\le1$. A learner retains a $B$-bit summary of the task; afterwards a query reveals unit vectors $x\in\mathbb R^n$, $p\in\mathbb R^m$, promising an update $H_*$ with $\operatorname{rank}H_*\le r$, $\|H_*\|_F\le\sqrt3$, $H_*x=p$ and $f(H_*)\le0$. From its summary, the query and coins only, the learner must return $H$ with $\operatorname{rank}H\le r$, $\|H\|_F\le\sqrt3$, $Hx=p$ and $f(H)\le\epsilon$, with probability at least $1-\beta$ for each fixed task and promised query. Let
--   $$
--   F_C=n^2\log_2\Big(1+\frac1{n\epsilon}\Big),\qquad F_R=nr\log_2\Big(1+\frac1{r\epsilon^2}\Big),\qquad\mathcal L=\log_2\frac2\epsilon,\qquad N_\beta=\Big\lceil\max\Big\{8192,\frac{512}{\sqrt{1-2\beta}}\Big\}\Big\rceil .
--   $$
--
--   **Theorem.** There is an absolute constant $C>0$ such that for every $0<\beta<1/2$ there is $c_\beta>0$ with the following property. For all $n\ge N_\beta$, $1\le r\le m\le n$, $0<\epsilon\le2^{-28}$ and every checkpoint $W_0$:
--
--   1. every width $B$ of a randomized protocol (arbitrary coins, joint randomized messages) that achieves the task satisfies $c_\beta(F_C+F_R)\le B$;
--   2. some deterministic code of width $B\le C\mathcal L^3(F_C+F_R)$ achieves the task with certainty, for every task and every promised query.
--
--   Hence
--   $$
--   c_\beta(F_C+F_R)\ \le\ B_{\mathrm{full}}(1,n,m,r;\epsilon,0,\sqrt3,\beta)\ \le\ C\mathcal L^3(F_C+F_R).
--   $$
--
--   The minimum memory for exactly fitting rank-$r$ updates that protect one old regression task to accuracy $\epsilon$ is thus characterized, up to a factor $O_\beta(\mathcal L^3)$, by a covariance term plus a response-rank term, far below the cost of storing the loss coefficients.
--
--   **Formalization Note** The two parts replace the infimum $B_{\mathrm{full}}$: part 2 shows the set of achieving widths is nonempty, so `sInf ∅ = 0` cannot make part 1 vacuous; a verification file derives the displayed two-sided bound for the infimum. A protocol is one coin space with an encoder that never sees the query and a decoder that never sees the history.
--
--   Differences from the source:
--   - encoding: c_β(F_C + F_R) ≤ B_full ≤ C𝓛³(F_C + F_R) with B_full the least register size → (i) every achieving width B satisfies c_β(F_C + F_R) ≤ B; (ii) an achieving code of width ≤ C𝓛³(F_C + F_R) exists; reason: (i) and (ii) imply (16) for the infimum (verification file) and exclude sInf ∅ = 0
--   - generalization: upper bound B_full ≤ C𝓛³(F_C + F_R) (randomized protocols, success probability 1 − β) → a deterministic code that succeeds with certainty; reason: the paper states the upper bound is deterministic (p.6) and proves it so in §C.5; it implies the B_full bound
--   - encoding: Section 1.2's retained-state convention → one coin space; encoder (history, coins), decoder (message, coins, query); measurable in the coins; success for every history and promised query; reason: the convention made explicit; public and private coins are components of the coin
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), Theorem 4, (15)–(16); §C.6, p.24 (PDF p.26), (71)

import Mathlib
import Definitions.Def_PreservePast_RandAchieves
import Definitions.Def_PreservePast_DetAchieves
import Definitions.Def_PreservePast_FC

open MeasureTheory

namespace PreservePast

universe u

/-- **Theorem 4 (the complete regression class at general rank).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8):
"Fix 0 < β < 1/2, and let N_β be a sufficiently large constant depending only on β, as specified in
(71). Suppose K = 1, ξ = 0, R = √3, n ≥ N_β, 1 ≤ r ≤ m ≤ n, 0 < ϵ ≤ 2^{−28}. Define
F_C = n² log₂(1 + 1/(nϵ)), F_R = nr log₂(1 + 1/(rϵ²)), 𝓛 = log₂(2/ϵ) (15). There are an absolute
constant C and a constant c_β > 0 such that c_β(F_C + F_R) ≤ B_full(1, n, m, r; ϵ, 0, √3, β)
≤ C𝓛³(F_C + F_R). (16) … The lower bound permits arbitrary joint randomized messages. The upper bound
is deterministic: for every fixed history and every promised unit query (x, p), it returns Hx = p,
rank H ≤ r, ‖H‖_F ≤ √3, and f(H) ≤ ϵ." (71), p.24: "N_β = ⌈max{8192, 512/√s_β}⌉", s_β = 1 − 2β.

There is an absolute constant `C > 0` such that for every `0 < β < 1/2` there is `c_β > 0` with the
following property. For all `n ≥ N_β`, `1 ≤ r ≤ m ≤ n`, `0 < ϵ ≤ 2^{−28}` and every checkpoint
`W₀ ∈ ℝ^{m×n}`, with one old task, exact fit (`ξ = 0`) and radius `R = √3`:
(i) every width `B` of a randomized protocol that succeeds with probability at least `1 − β` for
each fixed history and each promised query satisfies `c_β(F_C + F_R) ≤ B`;
(ii) some deterministic code of width `B ≤ C𝓛³(F_C + F_R)` succeeds with certainty for every task and
every promised query.

**Formalization Note.** (i) and (ii) together give (16) for `B_full = sInf` of the achieving widths
(derived in a verification file), and (ii) excludes the junk value `sInf ∅ = 0`. `C` is chosen
before `β`, `c_β` before the dimensions. The coin space of (i) is an arbitrary type. -/
theorem theorem_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ cβ : ℝ, 0 < cβ ∧
      ∀ (m n r : ℕ) (ε : ℝ) (W₀ : Matrix (Fin m) (Fin n) ℝ),
        Nbeta β ≤ n → 1 ≤ r → r ≤ m → m ≤ n → 0 < ε → ε ≤ (2 : ℝ) ^ (-28 : ℤ) →
        (∀ (B : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
            (enc : (Fin 1 → Task W₀) → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
            RandAchieves P enc dec r ε 0 (Real.sqrt 3) β → cβ * (FC n ε + FR n r ε) ≤ (B : ℝ)) ∧
        ∃ B : ℕ, (B : ℝ) ≤ C * calL ε ^ 3 * (FC n ε + FR n r ε) ∧
          ∃ (enc : (Fin 1 → Task W₀) → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
            DetAchieves enc dec r ε 0 (Real.sqrt 3) := by sorry

end PreservePast
