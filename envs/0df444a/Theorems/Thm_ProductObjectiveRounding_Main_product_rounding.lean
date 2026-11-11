-- Prove2me | Theorems.Thm_ProductObjectiveRounding_Main_product_rounding
-- name    : ProductObjectiveRounding.Main.product_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:42.027567+00:00
-- url     : https://prove2.me/theorems/ae0ec76e-9a4e-4b62-9426-cd36aee68882
-- title:
--   Theorem 1.1 — product rounding
-- statement:
--   For every fixed real $\varepsilon>0$, one finite deterministic exact-arithmetic arbitrary-CRCW program and positive constants $C_w,C_d$ and natural exponents $d,r$ work for every normalized nonnegative product input. It returns an explicitly written binary assignment satisfying
--   $$F(x)\le e^\varepsilon W,\quad \mathrm{work}\le C_w\max(1,N)L_2(n),\quad \mathrm{depth}\le C_dL(n)^d.$$
--   Here $n=|U|+k$ and $N=n+\sum_i|S_i|$. All arbitrary real endpoints and marginals are included, including integral marginals, zero endpoint factors, zero weights, empty supports and isolated variables. The program receives unsorted incidence records; preparation and output are charged. The same guarantees hold for every legal write-conflict resolution, with polynomial word/address ranges. There is no fair-sign or coefficient-mass hypothesis. Constants and the program may depend on fixed $\varepsilon$ only. This is the paper's full main theorem, with both resource clauses retained.
--
--   Differences from the source:
--   - encoding: finite supports and signs or binary assignments → distinct row-variable incidence identifiers over Fin labels; Bool assignments with explicit sign map; reason: every finite source input admits such an enumeration; sign values remain exactly minus one and one
--   - encoding: deterministic arbitrary-CRCW exact-arithmetic algorithm with asymptotic work and depth → one finite primitive program, universal legal write arbitration, operational work and synchronous PRAM depth, and a fixed polynomial word/address range; reason: makes the source computation model and uniform resource clauses explicit; no correctness or resource certificate is assumed
--   - encoding: logarithmic and doubly logarithmic asymptotic bounds → positive padded logarithms and max(1,size) with constants quantified before inputs; reason: accounts for bounded-size inputs, including zero size, without changing any asymptotic regime
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, Theorem 1.1, p.4

import Definitions.Def_ProductObjectiveRounding_Main_Specifications

namespace ProductObjectiveRounding.Main

/-- Theorem 1.1, p.4. One program for every normalized input, including arbitrary
real endpoints and marginals, zero weights, empty supports and isolated variables. -/
theorem product_rounding :
    ∀ ε : ℝ, 0 < ε →
    ∃ (P : PRAM.Program) (Cw Cd : ℝ) (d r : ℕ),
      0 < Cw ∧ 0 < Cd ∧
      ∀ I : ProductInput, I.Legal → ProductGuarantee P Cw Cd d r ε I := by sorry

end ProductObjectiveRounding.Main
