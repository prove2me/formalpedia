-- Prove2me | Theorems.Thm_ROLDescent_eq_70
-- name    : ROLDescent.eq_70
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:42.95804+00:00
-- url     : https://prove2.me/theorems/11ccce00-a034-4c64-8650-50f3a2fb07e4
-- title:
--   Eq. (70) — degree identities; $\pi_\tau$ is a probability and $P_\tau$ a reversible Markov matrix
-- statement:
--   Let $(X, w)$ be a weighted pure complex with facet size $d \ge 2$ and let $\tau$ be an internal face ($|\tau| + 2 \le d$), with link vertices $N_\tau$ and remaining rank $m_\tau = d - |\tau|$. Then:
--
--   1. $\sum_{i \in N_\tau} W_{\tau i} = m_\tau W_\tau$;
--   2. for every $i \in N_\tau$, $\sum_{j \in N_\tau,\, j \ne i} W_{\tau ij} = (m_\tau - 1) W_{\tau i}$;
--   3. $\pi_\tau(i) \ge 0$ for $i \in N_\tau$ and $\sum_{i \in N_\tau} \pi_\tau(i) = 1$;
--   4. for every $i \in N_\tau$, $P_\tau(i, j) \ge 0$ for $j \in N_\tau$ and $\sum_{j \in N_\tau} P_\tau(i,j) = 1$;
--   5. for distinct $i, j \in N_\tau$,
--   $$\pi_\tau(i) P_\tau(i,j) = \frac{W_{\tau ij}}{m_\tau (m_\tau - 1) W_\tau};$$
--   6. $\pi_\tau(i) P_\tau(i,j) = \pi_\tau(j) P_\tau(j, i)$ for all $i, j \in N_\tau$ (reversibility).
--
--   These identities make $P_\tau$ a reversible Markov chain with stationary law $\pi_\tau$, which is what allows the Markov-chain spectral gap to be used in the descent.
--
--   Differences from the source:
--   - reading: Σ_i W_τi and Σ_{j≠i} W_τij (index range not printed) → sums over the link vertices N_τ (and N_τ ∖ {i}); reason: the walk lives on N_τ; for j ∈ τ the literal set τij equals τi, so a sum over all of V is not what is meant
--   - encoding: π_τ is a probability distribution and P_τ is a Markov matrix → nonnegativity and sums equal to 1 on N_τ, at faces with τ.card + 2 ≤ d; reason: the definitions; π_τ and P_τ are defined at internal nodes
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (70), p.30 (PDF 30)

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_ROLDescent_facetMass
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_remRank
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_ROLDescent_linkWalk

namespace ROLDescent

/-- **Eq. (70): degree identities, π_τ a probability, P_τ a reversible Markov matrix.**
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (70), p.30 (PDF 30): "Counting the remaining vertices in each facet
gives Σ_i W_τi = m_τ W_τ, Σ_{j≠i} W_τij = (m_τ − 1) W_τi. Consequently π_τ is a probability
distribution and P_τ is a Markov matrix. It is reversible, since
π_τ(i) P_τ(i, j) = W_τij / (m_τ(m_τ − 1) W_τ) = π_τ(j) P_τ(j, i)."

**Formalization Note** At an internal face (τ.card + 2 ≤ d, i.e. m_τ ≥ 2). The sums range over the link
vertices `N_τ` (the sum over j ≠ i is over `N_τ \ {i}`; other vertices contribute `W_τij = 0` or are
in `τ`). The middle formula of the reversibility display is stated for `i ≠ j`; the reversibility
identity itself for all `i, j ∈ N_τ`. -/
theorem eq_70 {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∑ i ∈ HDXConc.linkVerts X τ, facetMass X d w (insert i τ) =
        (remRank d τ : ℝ) * facetMass X d w τ) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, ∑ j ∈ (HDXConc.linkVerts X τ).erase i, facetMass X d w (insert j (insert i τ)) =
        ((remRank d τ : ℝ) - 1) * facetMass X d w (insert i τ)) ∧
    ((∀ i ∈ HDXConc.linkVerts X τ, 0 ≤ outProb X d w τ i) ∧
        ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i = 1) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, (∀ j ∈ HDXConc.linkVerts X τ, 0 ≤ linkWalk X d w τ i j) ∧
        ∑ j ∈ HDXConc.linkVerts X τ, linkWalk X d w τ i j = 1) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, ∀ j ∈ HDXConc.linkVerts X τ, i ≠ j →
        outProb X d w τ i * linkWalk X d w τ i j =
          facetMass X d w (insert j (insert i τ)) /
            ((remRank d τ : ℝ) * ((remRank d τ : ℝ) - 1) * facetMass X d w τ)) ∧
    (∀ i ∈ HDXConc.linkVerts X τ, ∀ j ∈ HDXConc.linkVerts X τ,
        outProb X d w τ i * linkWalk X d w τ i j = outProb X d w τ j * linkWalk X d w τ j i) := by sorry

end ROLDescent
