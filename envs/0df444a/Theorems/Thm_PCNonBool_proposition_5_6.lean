-- Prove2me | Theorems.Thm_PCNonBool_proposition_5_6
-- name    : PCNonBool.proposition_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:32.959321+00:00
-- url     : https://prove2.me/theorems/4eed29cc-943e-44e5-a485-76394ff74f9a
-- title:
--   Proposition 5.6 (corrected: (a) needs every pigeon to have a hole) — constancy modulo $\langle A_i\rangle$ vs. $\langle \mathrm{PA}\cup\{x^2-1\}\rangle$; Qdeg = ppdeg
-- statement:
--   **Proposition 5.6.** Let $\mathbb F$ be a field of characteristic different from $2$ and $G=(U\sqcup V,E)$ a bipartite graph.
--
--   1. Suppose every pigeon has at least one hole. Then a monomial $m$ in the variables $\{x_{i,j}:j\in N(i)\}$ of a pigeon $i$ is constant modulo $\langle A_i\rangle$ if and only if it is constant modulo $\langle\mathrm{PA}\cup\{x_{i,j}^2-1 : i\in U,\ j\in N(i)\}\rangle$.
--   2. Consequently, the quadratic degree for FPHP$(G)$ coincides with the pairwise pigeon degree: for all monomials $m_1,m_2$,
--   $$\mathrm{Qdeg}(m_1,m_2)=\mathrm{ppdeg}(m_1,m_2).$$
--
--   Here a polynomial $q$ is constant modulo an ideal $I$ if $q-a\in I$ for some $a\in\mathbb F$. Part 2 is what lets the general splitting machinery of Section 4, phrased with Q-degree, be applied to FPHP$(G)$ with the simpler pairwise pigeon degree.
--
--   Differences from the source:
--   - correction: part (a) for every bipartite graph G → part (a) when every pigeon has at least one hole; reason: if some pigeon i' has N(i') = ∅, its parity axiom is 1 + 1 = 2, a unit, so every polynomial is constant modulo ⟨PA ∪ {x² − 1}⟩; but for a pigeon i with N(i) = {1, 2} the monomial x_{i,1} takes both values ±1 on the roots of A_i and is not constant modulo ⟨A_i⟩
--   - reading: ppdeg(m₀, m₁) = pdeg of the unique minimum-degree monomial in the class of m₀m₁ modulo ⟨PA ∪ {x² − 1}⟩ (Definition 5.5) → ppdegOn counts the pigeons i whose set H of holes occurring to an odd power in m₀m₁ is neither ∅ nor N(i); reason: the minimum-degree representative is not unique when |H| = |N(i)|/2, but whether pigeon i is mentioned is the same for every representative; when some pigeon has no hole the ideal is the unit ideal and the pigeon-by-pigeon count is still the Q-degree of Definition 4.9 (Proposition 5.6)
--   - encoding: (m₁)_{X_i}·(m₂)^{−1}_{X_i} not constant modulo ⟨A_i⟩ (Definition 4.9) → (m₁m₂)_{X_i} not constant modulo ⟨A_i⟩; reason: x² − 1 ∈ A_i, so the inverse of a monomial in X_i is congruent to the monomial itself
--   - encoding: "a monomial m in the variables {x_{i,j} : j ∈ N(i)}" (multilinear representatives) → any exponent vector supported on the edges of pigeon i; reason: both ideals contain x² − 1 for these variables, so a monomial and its multilinear representative are constant modulo them simultaneously
--   - reading: the section's field (characteristic ≠ 2) → ringChar F ≠ 2; reason: Section 5's standing assumption (Theorem 5.1, p.26)
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Proposition 5.6, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_ppdegOn
import Definitions.Def_PCNonBool_parityAxioms
import Definitions.Def_PCNonBool_localAxioms
import Definitions.Def_PCNonBool_qdegFPHP

namespace PCNonBool

/-- **Proposition 5.6** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.27 (PDF p.30)), corrected. Over a field of characteristic
`≠ 2`:

(a) if every pigeon has at least one hole, then a monomial `m` in the variables of pigeon `i` is
constant modulo `⟨A_i⟩` iff it is constant modulo `⟨PA ∪ {x_{i,j}² - 1}⟩`;

(b) the quadratic degree for FPHP(G) (Definition 4.9) coincides with the pairwise pigeon degree
(Definition 5.5) on every pair of monomials.

**Formalization Note** (a) as printed fails when another pigeon `i'` has no hole: its parity axiom
is `1 + 1 = 2`, so `⟨PA ∪ {x² - 1}⟩` is the unit ideal, while `x_{i,1}` is not constant modulo
`⟨A_i⟩` for `N(i) = {1, 2}`. "Constant modulo `I`" is `∃ a ∈ F, m - a ∈ I`. -/
theorem proposition_5_6 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2) (G : BipGraph U V) :
    ((∀ i' : U, (nbrOn G Finset.univ i').Nonempty) →
      ∀ (i : U) (m : Var G →₀ ℕ), (∀ e ∈ m.support, e.1.1 = i) →
        ((∃ a : F, MvPolynomial.monomial m 1 - MvPolynomial.C a ∈ Ideal.span (localAxioms G i)) ↔
         (∃ a : F, MvPolynomial.monomial m 1 - MvPolynomial.C a ∈
            Ideal.span (parityAxioms G ∪ Set.range (fun e : Var G => MvPolynomial.X e ^ 2 - 1))))) ∧
    ∀ m₁ m₂ : Var G →₀ ℕ, qdegFPHP F G m₁ m₂ = ppdegOn G Finset.univ Finset.univ s(m₁, m₂) := by sorry

end PCNonBool
