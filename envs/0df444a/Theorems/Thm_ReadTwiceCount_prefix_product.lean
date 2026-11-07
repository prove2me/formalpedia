-- Prove2me | Theorems.Thm_ReadTwiceCount_prefix_product
-- name    : ReadTwiceCount.prefix_product
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:44.080193+00:00
-- url     : https://prove2.me/theorems/d2ad21a6-9a8b-474f-b92f-dbc2ffee4bc9
-- title:
--   §3 (4) — the prefix probability $Q$ is the chain-rule product $c\prod_{I_-}(1-p_i)\prod_{I_+}p_i$
-- statement:
--   Let $H$ be a read-twice normalized state and $h$ a positive dangling query of $H$ whose variable occurs, in the clause $v$. Let $x_1,\dots,x_d$ be the other literals of $v$ and $H_i$ the prefix-conditioned states. Then:
--
--   1. whenever the variable of $x_i$ occurs in $H_i$, its remaining occurrence $z_i$ is a dangling query of $H_i$;
--   2. the probability $Q$, in $H-v$, that all $x_i$ are false is
--   $$Q=c\prod_{i\in I_-}(1-p_i)\prod_{i\in I_+}p_i,\qquad c=2^{-t},$$
--   where $p_i=p(H_i,z_i)$, $I_-$ holds the $\mathrm{NEQ}$ incidences, $I_+$ the $\mathrm{EQ}$ incidences, and $t$ is the number of free factors.
--
--   Each factor is evaluated in its own prefix-conditioned state. Together with (5), this identity turns the marginal of $h$ into a function of the children's marginals.
--
--   Differences from the source:
--   - encoding: states on the remaining variable universe → states on the original universe `Fin M`, pinned variables free; reason: pinning a variable keeps it in the universe as a free variable, which doubles both counts of every ratio and changes no probability
--   - encoding: a recognized zero prefix treated separately as $Q=0$; NEQ inputs with $p_i=0$ omitted → the product over all factors, inputs with $p_i=0$ included; reason: an EQ factor $p_i=0$ makes the product $0$ and a NEQ factor $1-p_i=1$ changes nothing; later prefix states of a zero prefix are unsatisfiable and Lean's $0/0=0$ gives them $p_i=0$, which does not change the zero product
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §3, display (4), pp.3–4

import Mathlib
import Definitions.Def_ReadTwiceCount_stateDesc

namespace ReadTwiceCount

/-- **The prefix product (4)** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §3, display (4), pp.3–4).
Let `h` be a positive dangling query whose variable occurs, in the clause `v` of a read-twice
normalized state `H`, and let `x₁, …, x_d` be the other literals of `v`. In the prefix-conditioned
state `Hᵢ` (`H − v` with `x₁, …, x_{i−1}` pinned false), the variable of `xᵢ` is free or has one
remaining occurrence `zᵢ`, which is then a dangling query of `Hᵢ`; and the probability `Q`, in
`H − v`, that all `xᵢ` are false is the chain-rule product
`Q = c ∏_{i∈I−} (1 − pᵢ) ∏_{i∈I+} pᵢ`, `c = 2^{−t}`, with `pᵢ = p(Hᵢ, zᵢ)`.

**Formalization Note** The product runs over all factors, including inputs with `pᵢ = 0`: an `EQ`
input with `pᵢ = 0` makes `Q = 0` (the zero prefix), a `NEQ` one contributes `1`. After a zero
factor the later prefix states are unsatisfiable and Lean's `0/0 = 0` gives them `pᵢ = 0`, which does
not change the (already zero) product. -/
theorem prefix_product {M : ℕ} (H : Formula M) (h : Lit M) (hRT : ReadTwice H)
    (hN : Normalized H) (hD : IsDangling H h) (hP : IsPositive H h) (hocc : H.occ h.1 = 1) :
    (∀ f ∈ factorsOf H h, ∀ (lbl : Label) (G : Formula M) (z : Lit M),
        f = Factor.input lbl G z → IsDangling G z) ∧
      prefixQ H h = ((factorsOf H h).map Factor.prob).prod := by sorry

end ReadTwiceCount
