-- Prove2me | Theorems.Thm_PhaseEncodedQGE_Supplement_theorem_5_3
-- name    : PhaseEncodedQGE.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:32:58.801455+00:00
-- url     : https://prove2.me/theorems/b7d373c1-0034-42eb-b499-021929b62671
-- title:
--   Theorem 5.3 — Weisfeiler–Leman placement of the first-order blocks and of the Taylor coefficients of defect layers
-- statement:
--   Let $G$ and $H$ be cubic graphs on $n$ vertices. Parts 1 and 2 concern one of the degree-prepared members PE-X1, PE-Y1, PE-X2 at fixed angles with $t>1$; part 3 concerns PE-QX1 (the Hadamard preparation with one $X$ mixer).
--
--   Folklore $k$-WL colours $k$-tuples $\bar u$ of vertices: $c_0(\bar u)$ is the atomic type (which entries coincide, which are adjacent) and $c_{\tau+1}(\bar u)=\big(c_\tau(\bar u),\{\{(c_\tau(\bar u[w/1]),\dots,c_\tau(\bar u[w/k])) : w\in V\}\}\big)$. One round does not distinguish $G$ from $H$ if the multisets of round-one colours of all $k$-tuples agree; $G$ and $H$ are $K$-WL equivalent if they agree after every round.
--
--   1. If one round of folklore $\max(m,2)$-WL does not distinguish $G$ from $H$, their first-order $m$-defect blocks $\{\{p_1(x)/p_0(x):|D(x)|=m\}\}$ coincide. On cubic graphs the pair census and the multiset of colours after one round of folklore 2-WL determine each other, so at angles satisfying the injectivity condition of Theorem 4.1 ($\Delta_k\ne0$, $\Delta_a/\Delta_k\notin\{-2,\dots,3\}$) the first-order two-defect blocks coincide iff one round of folklore 2-WL does not distinguish $G$ from $H$.
--   2. If $G$ and $H$ are $K$-WL equivalent, $K\ge2$, then for every $m\le K$ the Taylor coefficients of the $m$-defect layer agree as multisets jointly through order $K-m$, and the sorted $m$-defect blocks differ by
--   $$\big\|\mathrm{block}_m(G;\beta)-\mathrm{block}_m(H;\beta)\big\|_\infty=O(\beta^{K-m+1})\qquad(\beta\to0).$$
--   3. Under PE-QX1, if $G$ and $H$ are $K$-WL equivalent, $K\ge2$, then for every $m$ with $\min(m,n-m)\le K$ the multisets over the outcomes with $m$ defects of the Taylor coefficients through order $K-\min(m,n-m)$ coincide.
--
--   The theorem places the readout in the Weisfeiler–Leman hierarchy: at first order the $m$-defect block sees no more than one round of folklore $\max(m,2)$-WL, and the two-defect block sees exactly one round of folklore 2-WL; deeper agreement of the readouts follows from higher WL equivalence.
--
--   **Formalization Note** The colours are the published folklore colours `OAI.ParityWL.jointColor`, whose colour type does not depend on the graph. The sorted $m$-defect block is the block of ranks $K_{m-1}(n)+1,\dots,K_m(n)$; the $O(\beta^{K-m+1})$ statement is asserted entrywise, without a constant. "Fixed angles with $t>1$" is $0<\eta<\pi$ and $\tan(\eta/2)>1$.
--
--   Differences from the source:
--   - reading: "at fixed angles with $t>1$" → $0<\eta<\pi$ and $1<\tan(\eta/2)$; reason: the standing assumption of §2 (p.5), in force wherever layers, blocks and ranks are mentioned
--   - reading: "the pair census and the multiset of colours after one round of folklore 2-WL determine each other" → for cubic $G,H$ on the same vertex set: equal pair census $\Leftrightarrow$ equal multisets of round-one folklore 2-WL colours; reason: determining each other means each equality implies the other
--   - encoding: Taylor coefficients of the layer, normalized by $\mu_m$ (Corollary A.26(ii)) → unnormalized coefficient vectors $([\beta^j]p(x;\beta))_{0\le j\le J}$; reason: $\mu_m$ is common to the layer and nonzero, so the multisets agree in one form iff in the other
--   - encoding: $\|\mathrm{block}_m(G;\beta)-\mathrm{block}_m(H;\beta)\|_\infty=O(\beta^{K-m+1})$ → for every rank index $i$, the difference of the $i$-th entries is `IsBigO (𝓝 0)` of $\beta^{K-m+1}$; reason: the blocks have $\binom nm$ entries, so the entrywise and sup-norm statements are equivalent
--   - reading: part 3, "and no statement about ranks follows" → not formalized; reason: commentary; it asserts no theorem
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §5, pp.10–11 (PDF pp.11–12), Theorem 5.3 (= Corollary A.26, pp.24–25 (PDF pp.25–26), eq. (45)); folklore k-WL: §2, p.6 (PDF p.7), eq. (7)

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_PhaseEncodedQGE_SortedReadout
import Definitions.Def_PhaseEncodedQGE_Profile
import Definitions.Def_PhaseEncodedQGE_Supplement_GraphCounts
import Definitions.Def_PhaseEncodedQGE_Supplement_ClassValue
import Definitions.Def_PhaseEncodedQGE_Supplement_Readouts
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

open Filter Topology

/-- Theorem 5.3, Weisfeiler–Leman placement (Miller, Lee, *Structural Accessibility in
Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §5, pp.10–11;
appendix twin Corollary A.26, pp.24–25).

Let `G` and `H` be cubic graphs on `n` vertices. Parts (1) and (2) concern one of the
degree-prepared members PE-X1, PE-Y1, PE-X2 at fixed angles with `t > 1`; part (3) concerns PE-QX1.
1. If one round of folklore `max(m, 2)`-WL does not distinguish `G` from `H`, their first-order
   `m`-defect blocks coincide. On cubic graphs the pair census and the multiset of colours after one
   round of folklore 2-WL determine each other, so at angles satisfying the injectivity condition of
   Theorem 4.1 the first-order two-defect blocks coincide iff one round of folklore 2-WL does not
   distinguish `G` from `H`.
2. If `G` and `H` are `K`-WL equivalent, `K ≥ 2`, then for every `m ≤ K` the Taylor coefficients of
   the `m`-defect layer agree as multisets jointly through order `K − m`, and the sorted `m`-defect
   blocks differ by `O(β^{K−m+1})` as `β → 0`.
3. Under PE-QX1, if `G` and `H` are `K`-WL equivalent, `K ≥ 2`, then for every `m` with
   `min(m, n − m) ≤ K` the multisets over the outcomes with `m` defects of the Taylor coefficients
   through order `K − min(m, n − m)` coincide.

**Formalization Note** Folklore `k`-WL colours are the published `OAI.ParityWL.jointColor G k τ`
(platform definition `ParityLifts`): `c₀(ū)` records, for every ordered pair of positions, whether
the entries are equal and whether they are adjacent, and
`c_{τ+1}(ū) = (c_τ(ū), {{(c_τ(ū[w/1]), …, c_τ(ū[w/k])) : w ∈ V}})`, eq. (7), p.6; the colour type
`JointColor k τ` does not depend on the graph, so colours of `G` and `H` are compared directly.
"Not distinguished by one round" is equality of the multisets of round-one colours of all
`k`-tuples; "`K`-WL equivalent" is equality after every round `τ`. The first-order `m`-defect block
is `firstOrderBlock` (the multiset `{{p₁(x)/p₀(x) : |D(x)| = m}}`, Corollary A.26(i)); the Taylor
coefficients are `taylorLayer` (coefficient vectors `([β^j] p(x; β))_{0≤j≤J}` over the layer,
unnormalized: the paper's normalization by the common nonzero `µ_m` is equivalent); the sorted
`m`-defect block is the base `block` (ranks `K_{m−1}(n) + 1, …, K_m(n)`). "Differ by
`O(β^{K−m+1})` as `β → 0`" is, for every rank index `i`, `Asymptotics.IsBigO (𝓝 0)` of the
difference of the `i`-th entries against `β^{K−m+1}` (both blocks have `(n choose m)` entries, so
this is the sup-norm statement); no constant is asserted. Members are `IsDegMember γ P r h` with the
degree-aware preparation; "fixed angles with `t > 1`" is `0 < η < π` (standing assumption of §2,
p.5) and `1 < tan(η/2)`. The injectivity condition of Theorem 4.1 is
`∆_k ≠ 0 ∧ ∆_a/∆_k ∉ {−2, …, 3}` for the member's profile. The pair census is compared for every
`(a, k)` (it vanishes outside the seven classes on cubic graphs). PE-QX1 is the Hadamard preparation
with one `X` mixer, at every `γ`. The closing remark of part (3), "no statement about ranks
follows", is commentary and is not formalized. -/
theorem theorem_5_3 :
    -- (1) first part: one round of folklore max(m,2)-WL ⇒ equal first-order m-defect blocks
    (∀ (n m : ℕ) (η γ : ℝ) (P : Axis) (r : ℕ) (h : ℕ → ℝ), 0 < η → η < Real.pi →
      1 < Real.tan (η / 2) → IsDegMember γ P r h →
      ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        (Finset.univ : Finset (Fin (max m 2) → Fin n)).val.map
            (OAI.ParityWL.jointColor G (max m 2) 1) =
          (Finset.univ : Finset (Fin (max m 2) → Fin n)).val.map
            (OAI.ParityWL.jointColor H (max m 2) 1) →
        firstOrderBlock (degPrep G η) P r G γ m = firstOrderBlock (degPrep H η) P r H γ m) ∧
    -- (1) second part: pair census ⇔ round-one folklore 2-WL colour multiset, on cubic graphs
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)), IsCubic G → IsCubic H →
      ((∀ a k : ℕ, pairCensus G a k = pairCensus H a k) ↔
        (Finset.univ : Finset (Fin 2 → Fin n)).val.map (OAI.ParityWL.jointColor G 2 1) =
          (Finset.univ : Finset (Fin 2 → Fin n)).val.map (OAI.ParityWL.jointColor H 2 1))) ∧
    -- (1) last part: under the injectivity condition, equal two-defect blocks ⇔ one round of 2-WL
    (∀ (n : ℕ) (η γ : ℝ) (P : Axis) (r : ℕ) (h : ℕ → ℝ), 0 < η → η < Real.pi →
      1 < Real.tan (η / 2) → IsDegMember γ P r h →
      incrK h (Real.tan (η / 2)) ≠ 0 →
      (∀ z : ℤ, -2 ≤ z → z ≤ 3 →
        incrA h (Real.tan (η / 2)) / incrK h (Real.tan (η / 2)) ≠ (z : ℝ)) →
      ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        (firstOrderBlock (degPrep G η) P r G γ 2 = firstOrderBlock (degPrep H η) P r H γ 2 ↔
          (Finset.univ : Finset (Fin 2 → Fin n)).val.map (OAI.ParityWL.jointColor G 2 1) =
            (Finset.univ : Finset (Fin 2 → Fin n)).val.map (OAI.ParityWL.jointColor H 2 1))) ∧
    -- (2) K-WL equivalence ⇒ Taylor multisets through order K − m and O(β^{K−m+1}) blocks
    (∀ (n K m : ℕ) (η γ : ℝ) (P : Axis) (r : ℕ) (h : ℕ → ℝ), 0 < η → η < Real.pi →
      1 < Real.tan (η / 2) → IsDegMember γ P r h → 2 ≤ K → m ≤ K →
      ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        (∀ τ : ℕ, (Finset.univ : Finset (Fin K → Fin n)).val.map (OAI.ParityWL.jointColor G K τ) =
          (Finset.univ : Finset (Fin K → Fin n)).val.map (OAI.ParityWL.jointColor H K τ)) →
        taylorLayer (degPrep G η) P r G γ m (K - m) = taylorLayer (degPrep H η) P r H γ m (K - m) ∧
        ∀ i : ℕ, Asymptotics.IsBigO (𝓝 (0 : ℝ))
          (fun β : ℝ => (block (degPrep G η) P r G γ β m).getD i 0 -
            (block (degPrep H η) P r H γ β m).getD i 0)
          (fun β : ℝ => β ^ (K - m + 1))) ∧
    -- (3) PE-QX1: Taylor multisets through order K − min(m, n − m)
    (∀ (n K m : ℕ) (γ : ℝ), 2 ≤ K → min m (n - m) ≤ K →
      ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        (∀ τ : ℕ, (Finset.univ : Finset (Fin K → Fin n)).val.map (OAI.ParityWL.jointColor G K τ) =
          (Finset.univ : Finset (Fin K → Fin n)).val.map (OAI.ParityWL.jointColor H K τ)) →
        taylorLayer (hadPrep n) .X 1 G γ m (K - min m (n - m)) =
          taylorLayer (hadPrep n) .X 1 H γ m (K - min m (n - m))) := by sorry

end PhaseEncodedQGE.Supplement
