-- Prove2me | Theorems.Thm_TriFormQ_fact_2
-- name    : TriFormQ.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:57:13.499103+00:00
-- url     : https://prove2.me/theorems/0d0d9658-a4b8-4cd3-b9ea-fcc1741055ed
-- title:
--   Fact 2: on a good fiber, $\max_{u\in Z_v}\mathrm{rk} f[u]\le 2\lceil\mathrm{AR}(f)+5\log_q 2\rceil$
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F_q^n$, let $v$ be a good base point and $Z_v$ its (good) fiber. With $t=\lceil \mathrm{AR}(f)+5\log_q 2\rceil$,
--
--   $$\max_{u\in Z_v}\ \mathrm{rk}\, f[u]\ \le\ 2t .$$
--
--   Thus the linear space of slices $\{f[u]:u\in Z_v\}$ has bounded maximum rank, which is where the iterative pivot reduction of Theorem 7 starts.
--
--   Differences from the source:
--   - encoding: $\max_{u\in Z_v}\mathrm{rk}(f[u])\le 2t$ → $\mathrm{rk}(f[u])\le 2t$ for every $u\in Z_v$; reason: a bound on the maximum of a finite nonempty set
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Fact 2, p.30 (PDF p.33)

import Definitions.Def_TriFormQ_goodSet
import Definitions.Def_TriFormQ_fiber
import Definitions.Def_TriFormQ_sliceU

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Fact 2, p.30 (PDF p.33): "Let
t = ⌈AR(f) + 5 log_q 2⌉. For any good fiber Z_v of Z, max_{u∈Z_v} rk(f[u]) ≤ 2t."

**Formalization Note.** A good fiber is the fiber over a point of the good set (Definition 2);
`⌈·⌉₊` is the natural-number ceiling (its argument is nonnegative). -/
theorem fact_2 {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n) :
    ∀ v ∈ goodSet θ, ∀ u ∈ fiber θ v,
      (sliceU θ u).rank ≤ 2 * ⌈AR θ + 5 * Real.logb (Fintype.card F) 2⌉₊ := by sorry

end TriFormQ
