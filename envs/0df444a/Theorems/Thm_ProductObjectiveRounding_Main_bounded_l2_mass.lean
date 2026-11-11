-- Prove2me | Theorems.Thm_ProductObjectiveRounding_Main_bounded_l2_mass
-- name    : ProductObjectiveRounding.Main.bounded_l2_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:01.983553+00:00
-- url     : https://prove2.me/theorems/4eb82cde-d157-430f-a073-dfb4c9feccc5
-- title:
--   Lemma 4.4 — bounded ℓ2 mass
-- statement:
--   For every fixed $A\ge1$ and $a\in\mathbb N$, one deterministic program and positive resource constants work for every legal prepared fair-sign instance with ambient $n$, support size $m$, $1\le B\le A L(n)^a$, $0<\delta\le1$, $\delta^{-1}\le A L(n)^a$ and $\sum_{j\in S_i}b_{ij}^{2}\le B$ in every row. It returns signs satisfying
--   $$F(x)\le e^\delta W,\quad \mathrm{work}\le C_w\max(1,m)L_2(n),\quad \mathrm{depth}\le C_dL(n)^d.$$
--   All resource constants and exponents are uniform before the input. Coefficients of magnitude one and zero weights remain allowed. The square-mass bound extends the class handled by the absolute-mass milestone; positivity introduced during the source's preparation is not an input hypothesis.
--
--   Differences from the source:
--   - encoding: finite supports and signs or binary assignments → distinct row-variable incidence identifiers over Fin labels; Bool assignments with explicit sign map; reason: every finite source input admits such an enumeration; sign values remain exactly minus one and one
--   - encoding: deterministic arbitrary-CRCW exact-arithmetic algorithm with asymptotic work and depth → one finite primitive program, universal legal write arbitration, operational work and synchronous PRAM depth, and a fixed polynomial word/address range; reason: makes the source computation model and uniform resource clauses explicit; no correctness or resource certificate is assumed
--   - encoding: logarithmic and doubly logarithmic asymptotic bounds → positive padded logarithms and max(1,size) with constants quantified before inputs; reason: accounts for bounded-size inputs, including zero size, without changing any asymptotic regime
--   - encoding: parameters and reciprocal accuracy bounded by polylog n → every fixed A at least one and natural a, with a uniform program for parameters bounded by A L(n)^a; reason: quantifies all fixed polynomial envelopes; a common envelope includes any two separate ones
--   - encoding: fair-sign instance (5) held in the input representation of p.13, with an ambient n bounding its variables and rows, and the statement's parameters → an explicit ambient field with u+k ≤ ambient, validated incidence views (row and variable orders, boundaries, cross-pointers) and the real parameters serialized in the input; reason: p.13 maintains this representation for every fair-sign instance and fixes n as an ambient bound; every ambient bound on u+k is admitted, so every source instance is covered
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, Lemma 4.4, p.16

import Definitions.Def_ProductObjectiveRounding_Main_Specifications

namespace ProductObjectiveRounding.Main

/-- Lemma 4.4, p.16. Boundary coefficients and zero weights are allowed. -/
theorem bounded_l2_mass :
    ∀ A : ℝ, 1 ≤ A → ∀ a : ℕ,
    ∃ (P : PRAM.Program) (Cw Cd : ℝ) (d r : ℕ),
      0 < Cw ∧ 0 < Cd ∧
      ∀ (I : FairInput) (B δ : ℝ),
        I.Legal → 1 ≤ B → B ≤ A * L I.ambient ^ a →
        0 < δ → δ ≤ 1 → δ⁻¹ ≤ A * L I.ambient ^ a → I.MassBound 2 B →
        FairGuarantee P Cw Cd d r δ [B, δ] I := by sorry

end ProductObjectiveRounding.Main
