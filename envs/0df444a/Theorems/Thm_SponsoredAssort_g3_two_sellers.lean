-- Prove2me | Theorems.Thm_SponsoredAssort_g3_two_sellers
-- name    : SponsoredAssort.g3_two_sellers
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:03.075536+00:00
-- url     : https://prove2.me/theorems/ff3161e8-d141-42ae-a7eb-cf1214ba645d
-- title:
--   Appendix G.3, OA p.39 — two displayed sellers force a profile with ratio $r_j/r_i+o(1)$ (corrected: $r_j/r_i$)
-- statement:
--   Let $r>0$ with $r_i/r_{i+1}\ge n$ for all $i$, let $m$ satisfy (IC) and let $i<j$ be two sellers (so $r_i>r_j$). For every $\eta>0$ there is $\epsilon_0>0$ such that for all $0<\epsilon<\epsilon_0$: if $m$ displays at $v(\epsilon)$ an assortment $S$ containing both $i$ and $j$, then there is a profile $v''\ne0$ with $S(v'')=S$ and
--
--   $$
--   |R(S,v'')-r_j|\le\eta,\qquad |R(S\setminus\{j\},v'')-r_i|\le\eta,\qquad \frac{R(S,v'')}{R(m^{FB},v'')}\le\frac{r_j}{r_i}+\eta .
--   $$
--
--   Thus $\Delta(m,v'')\le R(S,v'')/R(S\setminus\{j\},v'')=r_j/r_i+o(1)$: insisting on two sellers near $0$ forces, through Corollary 5.1 applied to $i$ and then to $j$, an equally bad ratio at another profile.
--
--   Differences from the source:
--   - correction: $R(S,v'')/R(S\setminus\{j\},v'')=r_i/r_j+o(1)$ → $r_j/r_i+o(1)$; reason: the page's own limits $R(S,v'')\to r_j$ and $R(S\setminus\{j\},v'')\to r_i$ give $r_j/r_i$; e.g. $r=(2,1)$ gives $1/2$, not $2$
--   - reading: the explicit $v''(\epsilon)$ of the page → some profile $v''$ with $S(v'')=S$; reason: the printed asymptotics of $v''$ do not match its formula; the argument needs only such a profile
--   - encoding: $\to$ and $o(1)$ as $\epsilon\to0$ → tolerance $\eta$ for $0<\epsilon<\epsilon_0$, uniform in $S$; reason: definition of limits
--   - encoding: WLOG $r_i>r_j$; $r_i/r_{i+1}\ge n$ → $i<j$ (0-based); $n\,r_{i+1}\le r_i$; reason: with $r>0$ and $n\ge2$ the same conditions
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Appendix G.3, proof of Proposition 5.4, OA pp.38–39

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_firstBest
import Definitions.Def_SponsoredAssort_pointEps

open scoped NNReal

namespace SponsoredAssort

/-- **Appendix G.3, case of two displayed sellers** (Balseiro, Désir, SSRN 3821382
(Feb. 21, 2022), proof of Proposition 5.4, OA pp.38–39), corrected. Let `m` satisfy (IC), let
`r > 0` with `rᵢ/rᵢ₊₁ ≥ n` for all `i`, and let `i < j` be sellers. If `m` offers at
`v(ε) = (ε, (r₁/r₂)ε, …, (r₁/rₙ)ε)` an assortment `S` containing both `i` and `j`, then there is a
profile `v''(ε)` at which `m` still offers `S` and
`R(S, v''(ε)) / R(S^FB, v''(ε)) ≤ R(S, v''(ε)) / R(S \ {j}, v''(ε)) = rⱼ/rᵢ + o(1)` as `ε → 0`.

**Formalization Note.** The printed limit `rᵢ/rⱼ` is inverted: the text itself says
`R(S, v''(ε)) → rⱼ` and `R(S \ {j}, v''(ε)) → rᵢ`, so the ratio tends to `rⱼ/rᵢ < 1`. The `o(1)` is
an explicit tolerance: for every `η > 0` there is `ε₀ > 0` such that for all `0 < ε < ε₀` and every
such `S` some `w ≠ 0` has `S(w) = S`, `|R(S, w) − rⱼ| ≤ η`, `|R(S \ {j}, w) − rᵢ| ≤ η` and
`R(S, w) ≤ (rⱼ/rᵢ + η)·R(m^FB, w)`. Sellers are 0-based,
and `rᵢ/rᵢ₊₁ ≥ n` is written `n·rᵢ₊₁ ≤ rᵢ`. -/
theorem g3_two_sellers {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hratio : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → (n : ℝ) * r j ≤ r i)
    (m : Mechanism n) (hIC : IsIC r m) (i j : Fin n) (hij : i < j) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ≥0, 0 < ε₀ ∧ ∀ ε : ℝ≥0, 0 < ε → ε < ε₀ →
      ∀ S : Finset (Fin n), i ∈ S → j ∈ S → m.alloc (pointEps r ε) = S →
        ∃ w : Attr n, w ≠ 0 ∧ m.alloc w = S ∧
          |welfare r S w - r j| ≤ η ∧ |welfare r (S.erase j) w - r i| ≤ η ∧
          welfare r S w ≤ (r j / r i + η) * firstBest r w := by sorry

end SponsoredAssort
