-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_5_4_rank_from_expansion
-- name    : SemAC02.Supplement.theorem_5_4_rank_from_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:50:15.171388+00:00
-- url     : https://prove2.me/theorems/51b7733e-931b-4fe6-b9dd-78c3b59763fb
-- title:
--   Theorem 5.4 — rank of the expansion operator from boundary expansion
-- statement:
--   Let $G=(L\sqcup R,E)$ be an $(s,c)$-boundary expander given by a respectful clustered representation $F=F_0\cup\bigcup_{u\in L}F_u$ whose background axioms have a common Boolean zero, and let $R$ be the expansion operator of Definition 5.2 for a degree-compatible monomial order, defined up to degree $K$, where every axiom has degree at most $K\le cs/2-1$. Write $m=|L|$, $n=|R|$. Suppose every right cluster has the same size $D>0$ and every monomial with at most one variable from each cluster is irreducible modulo $\langle F_0\rangle$. Let $\kappa\ge1$ bound the degree of the graph on $L$ in which two vertices are adjacent when they share a right neighbour. For $1\le k\le\min\{K,n\}$ put $p=k/n$. If $4\kappa p^c<1$, then
--
--   $$
--   \operatorname{rank}(R_{\le k})\ \ge\ \Bigl(1-\frac{mp^c}{1-4\kappa p^c}\Bigr)\binom nk D^k. \tag{14}
--   $$
--
--   If the left and right degrees of $G$ are at most $\Delta_L$ and $\Delta_R$, one may take $\kappa=\max\{1,\Delta_L(\Delta_R-1)\}$.
--
--   This is the rank estimate used for random log-width CNFs (Theorem 7.2) and graph PHP (Theorem 7.5).
--
--   **Formalization Note** The axioms are multilinear polynomials over $\mathbb F_2$; $s$, $c$, $\kappa$ are real and $p^c$ is a real power. The second sentence is stated as the bound $\max\{1,\Delta_L(\Delta_R-1)\}$ on the degree of the graph on $L$.
--
--   Differences from the source:
--   - encoding: polynomial encoding in the Boolean ring B → axioms as multilinear polynomials over ZMod 2; reason: multilinear representatives of B
--   - encoding: R defined on standard monomials and extended linearly; rank(R_{≤k}) → expRank: dimension of the span of R(t) over standard monomials t of degree ≤ k; reason: the image of a linear map is spanned by the images of a basis; standard monomials of degree ≤ k span B_{F0}^{≤k} for a degree-compatible order
--   - encoding: normal form R_I(p), the unique combination of irreducible monomials → nf chooses such a combination with Classical.choose; reason: the combination is unique, so the choice is determined
--   - encoding: one may take κ = max{1, Δ_L(Δ_R − 1)} → conjunct: the degree of the graph on L is at most max 1 (Δ_L·(Δ_R − 1)) in ℕ; reason: admissibility of κ is exactly this degree bound; for Δ_R = 0 the graph has no edges
--   - generalization: §5.1 (p.38): F is the polynomial encoding of an unsatisfiable CNF formula, written as F₀ ∪ ⋃_u F_u → P : ClusteredRep — any set of multilinear polynomials over ZMod 2 split into F₀ and clusters F_u; no CNF or unsatisfiability hypothesis; reason: the rank count (fixed standard monomials over boundary-avoiding sets, (13)) uses only the stated hypotheses; every CNF encoding is such a clustered representation, so the statement specializes to the source
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 5.4, p.39 (PDF p.41); Definition 5.2, p.39 (PDF p.41); §5.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_Supplement_expansionRank

namespace SemAC02.Supplement

open MvPolynomial

/-- **Theorem 5.4 (Rank from boundary expansion)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–
Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission),
Theorem 5.4, p.39, for the operator of Definition 5.2, p.39): let `G = (L ⊔ R, E)` be an
`(s, c)`-boundary expander, and let `R` be the associated operator from Definition 5.2, defined up
to degree `K`. Write `m = |L|` and `n = |R|`. Suppose that every right cluster has the same
positive size `D` and every monomial containing at most one variable from each cluster is
irreducible modulo `⟨F₀⟩`. Let `κ ≥ 1` bound the maximum degree of the graph on `L` in which two
vertices are adjacent if they share a right neighbour. For `1 ≤ k ≤ min{K, n}` put `p = k/n`. If
`4κp^c < 1`, then `rank(R_{≤k}) ≥ (1 − mp^c/(1 − 4κp^c)) C(n, k) D^k` (14). If the left and
right degrees of `G` are at most `Δ_L` and `Δ_R`, respectively, one may take
`κ = max{1, Δ_L(Δ_R − 1)}`.

The standing conditions of Definition 5.2 (§5.1, pp.38–39) are hypotheses: the clustered
representation `P` (with its graph `G = P.graph`) is respectful, the background axioms have a
common Boolean zero, the monomial order is degree-compatible, every axiom has degree at most `K`,
and `K ≤ cs/2 − 1`.

**Formalization Note** The axioms are elements of `B` written as multilinear polynomials. `s`, `c`
and `κ` are real numbers, and `p^c` is the real power. `R_{≤k}` and its rank are `expRank`. The
second sentence is the second conjunct: the degree of every vertex of the graph on `L` is at most
`max{1, Δ_L(Δ_R − 1)}` (natural-number subtraction; `Δ_R = 0` forces an edgeless graph). -/
theorem theorem_5_4_rank_from_expansion {σ L R : Type} [Fintype σ] [DecidableEq σ] [Fintype L]
    [DecidableEq L] [Fintype R] [DecidableEq R]
    (P : ClusteredRep σ L R) (mo : MonomialOrder σ) (hmo : IsDegCompatible mo)
    (hml : ∀ f ∈ P.axioms, AC02Frege.IsMultilinear f)
    (hzero : ∃ y : σ → Bool, ∀ g ∈ P.F0, eval (toF2 y) g = 0)
    (hresp : P.IsRespectful)
    (s c : ℝ) (hexp : IsBdryExp P.graph s c)
    (K : ℕ) (hKdeg : ∀ f ∈ P.axioms, f.totalDegree ≤ K) (hKs : (K : ℝ) ≤ c * s / 2 - 1)
    (D : ℕ) (hD : 0 < D) (hcl : ∀ v : R, (Finset.univ.filter (fun x => P.cluster x = v)).card = D)
    (hirr : ∀ t : Finset σ, (∀ x ∈ t, ∀ y ∈ t, P.cluster x = P.cluster y → x = y) →
      IsIrred mo P.F0 t)
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hκdeg : ∀ u : L, ((Finset.univ.filter (fun u' => u' ≠ u ∧
      ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card : ℝ) ≤ κ)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) (hkn : k ≤ Fintype.card R)
    (hp : 4 * κ * ((k : ℝ) / Fintype.card R) ^ c < 1) :
    (1 - (Fintype.card L : ℝ) * ((k : ℝ) / Fintype.card R) ^ c /
        (1 - 4 * κ * ((k : ℝ) / Fintype.card R) ^ c)) *
        ((Fintype.card R).choose k : ℝ) * (D : ℝ) ^ k ≤ (expRank P mo s k : ℝ) ∧
    ∀ ΔL ΔR : ℕ, (∀ u, (PCNonBool.nbrOn P.graph Finset.univ u).card ≤ ΔL) →
      (∀ v, (Finset.univ.filter (fun u => P.graph.Adj u v)).card ≤ ΔR) →
      ∀ u : L, (Finset.univ.filter (fun u' => u' ≠ u ∧
        ∃ v, P.graph.Adj u v ∧ P.graph.Adj u' v)).card ≤ max 1 (ΔL * (ΔR - 1)) := by sorry

end SemAC02.Supplement
