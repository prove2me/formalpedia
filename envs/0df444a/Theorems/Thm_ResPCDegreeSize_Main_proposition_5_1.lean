-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_proposition_5_1
-- name    : ResPCDegreeSize.Main.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:34.792119+00:00
-- url     : https://prove2.me/theorems/4c12eed7-f646-4eac-9d8c-c98d56060198
-- title:
--   Proposition 5.1 — PC simulation of $\mathrm{Res}(\mathrm{PC}_r/\mathbb F_p)$
-- statement:
--   Let $\Pi$ be a $\mathrm{Res}(\mathrm{PC}_r/\mathbb F_p)$ refutation of a CNF $F$ and let $\mathcal C_D=\mathcal C_D(\mathcal Q(F))$. Put $d=(p-1)r$ and $\Delta=t(p-1)d$ with $t\ge1$. To every node $L$ of $\Pi$ attach
--   $$P_L=\prod_{j=1}^t(1-q_{L,j}^{p-1}),\qquad q_{L,j}\in\mathrm{span}_{\mathbb F_p}\{g_h:h\in L\},\tag{42}$$
--   where $g_h=\mathrm{ML}(1-h^{p-1})$, and let $f$ satisfy $\deg f\le K$ and
--   $$fP_Lg_h\in\mathcal C_D\quad\text{for every node }L\text{ and every equation }h\text{ of }L.\tag{43}$$
--   If
--   $$K+\max\{2\Delta+2d,\ \Delta+w(F)\}\le D,\tag{46}$$
--   then
--   $$fP_L\in\mathcal C_D\quad\text{for every line }L\text{ of }\Pi.$$
--   In particular, $f\in\mathcal C_D$.
--
--   The whole refutation is thus replayed inside degree-$D$ polynomial calculus, with $f$ as a common multiplier.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - generalization: a Res(PC_r/F_p) refutation is a finite DAG of disjunctions, with weakening, contraction, deletion of false constants, linear combination and multiplication, and S counts its nodes → lines are Finsets of polynomials of degree at most r (contraction and reordering are built in, weakening is ⊆), a refutation is a list whose entries follow from earlier entries and whose last entry is empty, unreachable entries are allowed, and S is the list length; reason: each paper refutation maps node by node to a list refutation with at most as many entries, so the Lean statement covers every paper refutation; the multiplier g of the multiplication rule carries no separate degree bound because deg(fg) ≤ r bounds it when f ≠ 0 and the line is unchanged when f = 0
--   - generalization: "as above": the hypotheses of Theorem 4.3 including 1 ∉ C_D and S(1−η)^t < 1, with P_L and f produced by that theorem → any factors q_{L,j} in the spans (42) and any f with deg f ≤ K and (43); only t ≥ 1 and (46) remain; reason: the proof uses nothing else, and the polynomials produced by Theorem 4.3 are an instance
--   - encoding: equations of a line indexed by i ∈ [m_L], with g_{L,i} = g_{h_{L,i}} → equations are the elements h of the Finset line, and g_{L,i} is indicator h; reason: repeated disjuncts have equal indicators, so the spans and the conditions (43) are the same
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Proposition 5.1, eq. (46), PDF p. 10 (printed p. 9); setting (40)–(43), PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_ResolutionOverPolynomials
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem proposition_5_1 {n p r t d Δ D K : ℕ} [Fact p.Prime] (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hd : d = (p - 1) * r) (hΔ : Δ = t * (p - 1) * d)
    (F : CNF n) (R : ResRefutation p F r)
    (q : Fin R.size → Fin t → Poly n p)
    (hq : ∀ ν j, q ν j ∈
      Submodule.span (ZMod p) (indicator '' (R.line ν : Set (Poly n p))))
    (f : Poly n p) (hf : f.totalDegree ≤ K)
    (h43 : ∀ ν, ∀ h ∈ R.line ν,
      f * rsProduct (q ν) * indicator h ∈ CD (encoding p F) D)
    (h46 : K + max (2 * Δ + 2 * d) (Δ + width F) ≤ D) :
    (∀ ν, f * rsProduct (q ν) ∈ CD (encoding p F) D) ∧ f ∈ CD (encoding p F) D := by sorry

end ResPCDegreeSize.Main
