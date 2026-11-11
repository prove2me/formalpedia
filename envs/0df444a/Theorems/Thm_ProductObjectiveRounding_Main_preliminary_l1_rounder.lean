-- Prove2me | Theorems.Thm_ProductObjectiveRounding_Main_preliminary_l1_rounder
-- name    : ProductObjectiveRounding.Main.preliminary_l1_rounder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:39.263506+00:00
-- url     : https://prove2.me/theorems/0a75f45c-1798-4f10-9380-af06096f57e0
-- title:
--   Lemma 4.2 — preliminary ℓ1 rounder
-- statement:
--   There is one deterministic program with absolute positive constants $C_w,C_d$ and natural exponents $a,d,r$. For every legal prepared fair-sign instance with ambient size $n$ and support size $m$, every $B\ge1$ and $0<\alpha\le1$ with $\sum_{j\in S_i}|b_{ij}|\le B$ for each row, it outputs signs satisfying
--   $$F(x)\le e^\alpha W,\quad \mathrm{work}\le C_w\max(1,m)B^{12}\alpha^{-8}(1+\log(2+nB/\alpha))^a,\quad \mathrm{depth}\le C_d(1+B/\alpha+L(n))^d.$$
--   The word/address exponent is fixed before all inputs. The parameters $B,\alpha$ are supplied real input values, not fixed accuracy promises. No polylogarithmic restriction is placed on them. This is the preliminary rounder used at finer accuracies in later constructions.
--
--   Differences from the source:
--   - encoding: finite supports and signs or binary assignments → distinct row-variable incidence identifiers over Fin labels; Bool assignments with explicit sign map; reason: every finite source input admits such an enumeration; sign values remain exactly minus one and one
--   - encoding: deterministic arbitrary-CRCW exact-arithmetic algorithm with asymptotic work and depth → one finite primitive program, universal legal write arbitration, operational work and synchronous PRAM depth, and a fixed polynomial word/address range; reason: makes the source computation model and uniform resource clauses explicit; no correctness or resource certificate is assumed
--   - encoding: logarithmic and doubly logarithmic asymptotic bounds → positive padded logarithms and max(1,size) with constants quantified before inputs; reason: accounts for bounded-size inputs, including zero size, without changing any asymptotic regime
--   - encoding: fair-sign instance (5) held in the input representation of p.13, with an ambient n bounding its variables and rows, and the statement's parameters → an explicit ambient field with u+k ≤ ambient, validated incidence views (row and variable orders, boundaries, cross-pointers) and the real parameters serialized in the input; reason: p.13 maintains this representation for every fair-sign instance and fixes n as an ambient bound; every ambient bound on u+k is admitted, so every source instance is covered
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, Lemma 4.2, p.13

import Definitions.Def_ProductObjectiveRounding_Main_Specifications

namespace ProductObjectiveRounding.Main

/-- Lemma 4.2, p.13. No polylogarithmic restriction on B or reciprocal accuracy. -/
theorem preliminary_l1_rounder :
    ∃ (P : PRAM.Program) (Cw Cd : ℝ) (a d r : ℕ),
      0 < Cw ∧ 0 < Cd ∧
      ∀ (I : FairInput) (B α : ℝ),
        I.Legal → 1 ≤ B → 0 < α → α ≤ 1 → I.MassBound 1 B →
        PreliminaryGuarantee P Cw Cd a d r B α I := by sorry

end ProductObjectiveRounding.Main
