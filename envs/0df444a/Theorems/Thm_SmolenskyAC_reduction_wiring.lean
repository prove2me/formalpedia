-- Prove2me | Theorems.Thm_SmolenskyAC_reduction_wiring
-- name    : SmolenskyAC.reduction_wiring
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:53.687328+00:00
-- url     : https://prove2.me/theorems/d9355394-2293-4c3b-a3a6-1255f507714b
-- title:
--   Reductions 1) and 4) — $\mathrm{MOD}_{s,q}=\mathrm{NOT}\,\mathrm{MOD}_r\circ\sigma_s$ by explicit wiring when $q\mid r$
-- statement:
--   Let $q,r\ge1$ with $q\mid r$, put $a=r/q$, and let $s<q$, $n\ge0$ and $m\ge a(n+q)$. Let $\sigma_s:D^n\to D^m$ put each input $x_i$ on $a$ wires, the constant $1$ on $a(q-s)$ further wires and $0$ on the rest. Then for every $x\in D^n$
--
--   $$\mathrm{MOD}_{s,q}(x)=\mathrm{NOT}\,\mathrm{MOD}_r\big(\sigma_s(x)\big).$$
--
--   For $r=q$ it gives reduction 1) ($\mathrm{MOD}_{s,q}$ from $\mathrm{MOD}_q$), and for $s=0$ reduction 4) ($\mathrm{MOD}_q(x)=\mathrm{MOD}_r(\sigma_0(x))$ when $q\mid r$). The reduction is one gate deep, so it costs no depth when composed with a circuit for $\mathrm{MOD}_r$.
--
--   Differences from the source:
--   - reading: MOD_(s,p) for s < p is AC^0 reducible to MOD_p; MOD_a is AC^0 reducible to MOD_b when a | b → an explicit wiring σ_s into one MOD_r gate followed by NOT, for every m ≥ (r/q)(n+q); reason: it is a constant depth, polynomial size circuit as the page's definition asks, and the proof of Theorem 2 needs its depth
--   - generalization: reduction 1) for a modulus p → any modulus q ≥ 1 and any multiple r of q; reason: p is one case of q, and r = q gives reduction 1)
--   - encoding: moduli q and r → 0 < q, 0 < r; reason: modulus 0 is undefined
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Basic Notation and Definitions, reductions 1) and 4), p.78 (pdf 2)

import Mathlib
import Definitions.Def_SmolenskyAC_Wiring

namespace SmolenskyAC

/-- **Reductions 1) and 4)** (Smolensky, STOC 1987, "Basic Notation and Definitions", p.78), in
explicit depth-preserving form: for `0 < q`, `0 < r`, `q ∣ r`, `s < q`, every `n` and every
`m ≥ (r/q)·(n + q)`, the function `MOD_{s,q}` on `n` inputs is the negation of one `MOD_r` gate on
`m` wires, each input `x_i` on `r/q` wires, `(r/q)·(q − s)` wires carrying `1` and the rest `0`:
`MOD_{s,q}(x) = NOT MOD_r(σ_s(x))`.

**Formalization Note.** `AC^0` reducibility is replaced by the explicit wiring `σ_s = wiring`,
which gives the page's reductions (`r = q` for 1), `s = 0` for 4)) and, unlike a composed
reduction circuit, adds no gate below the `MOD_r` gate. -/
theorem reduction_wiring (q r s n m : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ∣ r) (hs : s < q)
    (hm : r / q * (n + q) ≤ m) (x : Cube n) :
    MODs s q n x = !(MODp r m (wiring (r / q) q s n m x)) := by sorry

end SmolenskyAC
