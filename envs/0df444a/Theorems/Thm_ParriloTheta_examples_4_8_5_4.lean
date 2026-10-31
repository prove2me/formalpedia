-- Prove2me | Theorems.Thm_ParriloTheta_examples_4_8_5_4
-- name    : ParriloTheta.examples_4_8_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:18.773529+00:00
-- url     : https://prove2.me/theorems/a3ff5bbe-4c5b-4e2b-b637-113f5243d3ed
-- title:
--   Examples 4.8 and 5.4 (with p.24) — $C_{2n+1}$ and $\overline{C_{2n+1}}$ have $\vartheta$-rank $1$
-- statement:
--   Let $n\ge2$, let $C_{2n+1}$ be the cycle on $2n+1$ nodes and $\overline{C_{2n+1}}$ its complement. Then:
--   1. $\vartheta\text{-rank}(C_{2n+1})=1$ and $\vartheta\text{-rank}(\overline{C_{2n+1}})=1$;
--   2. for every node $i$, $\vartheta\text{-rank}(C_{2n+1}\setminus i^\perp)=0$ and $\vartheta\text{-rank}(\overline{C_{2n+1}}\setminus i^\perp)=0$;
--   3. $C_{2n+1}$ is critical and connected, and it is not a clique;
--   4. the critical edges of $\overline{C_{2n+1}}$ are exactly the pairs $\{i,i+2\}$ (indices modulo $2n+1$), and the graph they form is connected and is not a clique.
--
--   These are the hypotheses of Theorems 6.6 and 6.13 for $H=C_{2n+1}$ and $H=\overline{C_{2n+1}}$, from which Corollary 6.14 follows. Item 2 is asserted on p.24 ("As pointed out in Example 4.8").
--
--   **Formalization Note** $C_{2n+1}$ is Mathlib's `cycleGraph (2 * n + 1)` on `Fin (2n+1)`, so $i+2$ is computed modulo $2n+1$.
--
--   Differences from the source:
--   - encoding: C_{2n+1} on nodes 1, …, 2n+1 → cycleGraph (2 * n + 1) on Fin (2n+1); complement ᶜ; reason: Lean convention; same graphs
--   - encoding: ϑ-rank(G) ∈ ℕ ∪ {∞} → thetaRank G : ℕ∞ (⊤ = ∞); reason: Lean convention; same values
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Example 4.8, p.11; Example 5.4, p.12; proof of Corollary 6.14, p.24

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ParriloTheta_thetaRank
import Definitions.Def_ParriloTheta_delNbhd

namespace ParriloTheta

open ChvatalPolytopes.Separation SimpleGraph

/-- **Examples 4.8 and 5.4: odd cycles and their complements have ϑ-rank 1.**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Example 4.8, p.11: "As an application of Lemma 4.7 we obtain that
ϑ-rank(C2n+1) ≤ 1 and ϑ-rank(C̄2n+1) ≤ 1." Example 5.4, p.12: "Let n ≥ 2. … their ϑ-rank is equal
1. (i) The graph C2n+1 is critical and connected (and not a clique) … (ii) The critical edges of
the graph G = C̄2n+1 are those of the form {i, i + 2} … Hence the subgraph Gc (of critical edges)
is connected (and not a clique)". Proof of Corollary 6.14, p.24: "As pointed out in Example 4.8, H
satisfies the property: ϑ-rank(H \ i⊥) = 0 for all i ∈ V".

For every `n ≥ 2`, with `H₁ = C_{2n+1}` and `H₂ = C̄_{2n+1}`: `ϑ-rank(H₁) = ϑ-rank(H₂) = 1`,
`ϑ-rank(H₁ \ i⊥) = ϑ-rank(H₂ \ i⊥) = 0` for every node `i`, `H₁` is critical, connected and not a
clique, the critical edges of `H₂` are exactly the pairs `{i, i + 2}` (indices modulo `2n + 1`),
and they form a connected graph that is not a clique.

**Formalization Note.** `C_{2n+1}` is Mathlib's `cycleGraph (2 * n + 1)` on `Fin (2n+1)`; the
complement is `ᶜ`; `i + 2` is addition in `Fin (2n+1)`, i.e. modulo `2n + 1`. "Critical" and
`G_c` are the published `IsAlphaCritical`, `IsCriticalEdge` and `criticalGraph`. -/
theorem examples_4_8_5_4 (n : ℕ) (hn : 2 ≤ n) :
    thetaRank (cycleGraph (2 * n + 1)) = 1 ∧
    thetaRank ((cycleGraph (2 * n + 1))ᶜ) = 1 ∧
    (∀ i, thetaRank (delNbhd (cycleGraph (2 * n + 1)) i) = 0) ∧
    (∀ i, thetaRank (delNbhd ((cycleGraph (2 * n + 1))ᶜ) i) = 0) ∧
    IsAlphaCritical (cycleGraph (2 * n + 1)) ∧ (cycleGraph (2 * n + 1)).Connected ∧
    ¬ (cycleGraph (2 * n + 1)).IsClique Set.univ ∧
    (∀ e : Sym2 (Fin (2 * n + 1)), IsCriticalEdge ((cycleGraph (2 * n + 1))ᶜ) e ↔
      ∃ i : Fin (2 * n + 1), e = s(i, i + 2)) ∧
    (criticalGraph ((cycleGraph (2 * n + 1))ᶜ)).Connected ∧
    ¬ (criticalGraph ((cycleGraph (2 * n + 1))ᶜ)).IsClique Set.univ := by sorry

end ParriloTheta
