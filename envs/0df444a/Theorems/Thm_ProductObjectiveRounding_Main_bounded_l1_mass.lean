-- Prove2me | Theorems.Thm_ProductObjectiveRounding_Main_bounded_l1_mass
-- name    : ProductObjectiveRounding.Main.bounded_l1_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:25.885415+00:00
-- url     : https://prove2.me/theorems/87404ba1-a19f-4476-9ecf-61eccb8af938
-- title:
--   Lemma 4.3 — bounded ℓ1 mass
-- statement:
--   For every fixed $A\ge1$ and $a\in\mathbb N$, one deterministic program and positive resource constants work for every legal prepared fair-sign instance with ambient $n$, support size $m$, $1\le B\le A L(n)^a$, $0<\delta\le1$, $\delta^{-1}\le A L(n)^a$ and $\sum_{j\in S_i}|b_{ij}|\le B$ in every row. Its explicit output satisfies
--   $$F(x)\le e^\delta W,\quad \mathrm{work}\le C_w\max(1,m)L_2(n),\quad \mathrm{depth}\le C_dL(n)^d.$$
--   The program, constants, depth exponent and polynomial word/address exponent depend only on the fixed envelope, not on the instance, numerical magnitudes, $B$ or $\delta$. This milestone gives the improved work bound under an absolute-mass restriction.
--
--   Differences from the source:
--   - encoding: finite supports and signs or binary assignments → distinct row-variable incidence identifiers over Fin labels; Bool assignments with explicit sign map; reason: every finite source input admits such an enumeration; sign values remain exactly minus one and one
--   - encoding: deterministic arbitrary-CRCW exact-arithmetic algorithm with asymptotic work and depth → one finite primitive program, universal legal write arbitration, operational work and synchronous PRAM depth, and a fixed polynomial word/address range; reason: makes the source computation model and uniform resource clauses explicit; no correctness or resource certificate is assumed
--   - encoding: logarithmic and doubly logarithmic asymptotic bounds → positive padded logarithms and max(1,size) with constants quantified before inputs; reason: accounts for bounded-size inputs, including zero size, without changing any asymptotic regime
--   - encoding: parameters and reciprocal accuracy bounded by polylog n → every fixed A at least one and natural a, with a uniform program for parameters bounded by A L(n)^a; reason: quantifies all fixed polynomial envelopes; a common envelope includes any two separate ones
--   - encoding: fair-sign instance (5) held in the input representation of p.13, with an ambient n bounding its variables and rows, and the statement's parameters → an explicit ambient field with u+k ≤ ambient, validated incidence views (row and variable orders, boundaries, cross-pointers) and the real parameters serialized in the input; reason: p.13 maintains this representation for every fair-sign instance and fixes n as an ambient bound; every ambient bound on u+k is admitted, so every source instance is covered
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, Lemma 4.3, p.14

import Definitions.Def_ProductObjectiveRounding_Main_Specifications

namespace ProductObjectiveRounding.Main

/-- Lemma 4.3, p.14. Every fixed polynomial envelope, uniformly over its inputs. -/
theorem bounded_l1_mass :
    ∀ A : ℝ, 1 ≤ A → ∀ a : ℕ,
    ∃ (P : PRAM.Program) (Cw Cd : ℝ) (d r : ℕ),
      0 < Cw ∧ 0 < Cd ∧
      ∀ (I : FairInput) (B δ : ℝ),
        I.Legal → 1 ≤ B → B ≤ A * L I.ambient ^ a →
        0 < δ → δ ≤ 1 → δ⁻¹ ≤ A * L I.ambient ^ a → I.MassBound 1 B →
        FairGuarantee P Cw Cd d r δ [B, δ] I := by sorry

end ProductObjectiveRounding.Main
