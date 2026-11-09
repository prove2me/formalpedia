-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_theorem_4_3
-- name    : ResPCDegreeSize.Main.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:25:58.998208+00:00
-- url     : https://prove2.me/theorems/e7a3507f-83b5-4ad7-ac61-aa0f3a415f21
-- title:
--   Theorem 4.3 — common multiplier
-- statement:
--   Let $Q\supseteq\mathrm{Bool}$ and $\mathcal C_D=\mathcal C_D(Q)$. Suppose $1\notin\mathcal C_D$ and the parameters $t,d,K$ satisfy $t\ge1$, $d\le K\le n$ and $K+d+(p-1)dt\le D$. Let $S\ge1$ and for each $\nu\in[S]$ let $(g_{\nu,i})_{i=1}^{m_\nu}$ be a family of polynomials of degree at most $d$. Write
--   $$\eta=\Bigl(1-\frac1p\Bigr)\frac{N_n(K-d)}{N_n(K)},\qquad h_K=\dim V_K/\mathcal C_{\le K}.\tag{36}$$
--   Then for each $\nu$ there is a polynomial $P_\nu=\prod_{j=1}^t(1-q_{\nu,j}^{p-1})$ with every $q_{\nu,j}\in\mathrm{span}_{\mathbb F_p}\{g_{\nu,i}\}_i$ such that
--   $$c_{P_\nu}(K)\le h_K(1-\eta)^t.\tag{37}$$
--   In particular, if
--   $$S(1-\eta)^t<1,\tag{38}$$
--   then there is a multilinear $f\in V_K$ such that
--   $$f\notin\mathcal C_D,\qquad fg_{\nu,i}P_\nu\in\mathcal C_D\quad\text{for all }\nu,i.\tag{39}$$
--
--   The same polynomials $P_\nu$ serve both conclusions. This produces the approximators and the multiplier of the simulation in Section 5.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: classes in V_D/C_D → classes in the quotient of the whole ring F_p[x] by C_D; reason: C_D ⊆ V_D, so V_D/C_D embeds in that quotient and every kernel and rank is unchanged; the degree bounds of the statement keep every product inside V_D
--   - encoding: there exists P_ν of the form (24) with t factors → the factors q_{ν,j} are the witnesses and P_ν is rsProduct (q ν); reason: this is the form (24) literally, and the single existential keeps the same P_ν in (37) and (39)
--   - encoding: h_K = dim V_K/C_{≤K} → finrank of the quotient of V_K by the preimage of C_D under the inclusion; reason: that preimage is C_D ∩ V_K = C_{≤K}
--   - encoding: F_p[x_1,…,x_n]; ν ∈ [S], i ∈ [m_ν], j ∈ [t] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; Fin S, Fin (m ν), Fin t; reason: relabelling of the indices; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Theorem 4.3, eqs. (36)–(39), PDF pp. 8–9 (printed pp. 7–8)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem theorem_4_3 {n p t d K D S : ℕ} [Fact p.Prime]
    (Q : Set (Poly n p)) (hQ : boolAxioms n p ⊆ Q)
    (h1 : (1 : Poly n p) ∉ CD Q D) (ht : 1 ≤ t) (hdK : d ≤ K) (hKn : K ≤ n)
    (hD : K + d + (p - 1) * d * t ≤ D) (hS : 1 ≤ S)
    (m : Fin S → ℕ) (g : ∀ ν : Fin S, Fin (m ν) → Poly n p)
    (hg : ∀ ν i, (g ν i).totalDegree ≤ d) :
    ∃ q : Fin S → Fin t → Poly n p,
      (∀ ν j, q ν j ∈ Submodule.span (ZMod p) (Set.range (g ν))) ∧
      (∀ ν, (cRank Q D (g ν) (rsProduct (q ν)) K : ℝ) ≤
        (hDim Q D K : ℝ) * (1 - eta p n K d) ^ t) ∧
      ((S : ℝ) * (1 - eta p n K d) ^ t < 1 →
        ∃ f : Poly n p, f ∈ V n p K ∧ IsMultilinear f ∧ f ∉ CD Q D ∧
          ∀ ν i, f * g ν i * rsProduct (q ν) ∈ CD Q D) := by sorry

end ResPCDegreeSize.Main
