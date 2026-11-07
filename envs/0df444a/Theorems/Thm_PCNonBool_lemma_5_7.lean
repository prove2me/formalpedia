-- Prove2me | Theorems.Thm_PCNonBool_lemma_5_7
-- name    : PCNonBool.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:24.770678+00:00
-- url     : https://prove2.me/theorems/d98cf100-9932-492b-8a52-37ddc0068115
-- title:
--   Lemma 5.7 — pairwise pigeon degree $D \ge 2$ gives pigeon degree $\le 6D$
-- statement:
--   **Lemma 5.7.** Let $\mathbb F$ be a field of characteristic different from $2$, $G$ a bipartite graph and $D\ge2$. If FPHP$(G)$ has a polynomial calculus refutation of pairwise pigeon degree at most $D$, then FPHP$(G)$ has a polynomial calculus refutation of pigeon degree at most $6D$.
--
--   This is the instance for FPHP$(G)$ of the paper's general conversion from quadratic degree to support degree (Lemma 4.19, with fan-in $2$). It turns the low pairwise pigeon degree produced by Algorithm 1 into low pigeon degree, which Corollary 5.4 forbids.
--
--   Differences from the source:
--   - encoding: "FPHP(G) can be refuted in pairwise pigeon degree D ≥ 2" / "in pigeon degree at most 6D" → ∃ refutation π with ppdeg(π) ≤ D (D real, 2 ≤ D) / ∃ refutation π' with pdeg(π') ≤ 6D; reason: the degrees are integers, so a real D gives the same statements as ⌊D⌋ with the weaker bound 6D ≥ 6⌊D⌋
--   - reading: ppdeg(m₀, m₁) = pdeg of the unique minimum-degree monomial in the class of m₀m₁ modulo ⟨PA ∪ {x² − 1}⟩ (Definition 5.5) → ppdegOn counts the pigeons i whose set H of holes occurring to an odd power in m₀m₁ is neither ∅ nor N(i); reason: the minimum-degree representative is not unique when |H| = |N(i)|/2, but whether pigeon i is mentioned is the same for every representative; when some pigeon has no hole the ideal is the unit ideal and the pigeon-by-pigeon count is still the Q-degree of Definition 4.9 (Proposition 5.6)
--   - reading: the section's field (characteristic ≠ 2) → ringChar F ≠ 2; reason: Section 5's standing assumption (Theorem 5.1, p.26)
--   - reading: polynomial calculus (refutations on both sides of the statement) → the mission's PC model on both sides: lines reduced modulo the range axioms, axiom lines c·red(a) with c ∈ F, fan-in 2, refutation = derivation containing 1; reason: one PC model is used throughout the mission; it is the model the paper's own splitting and restriction steps (Lemmas 5.9, 5.13) need
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: refutation = derivation of the constant polynomial 1 → IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size or degree
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.7, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_fphp
import Definitions.Def_PCNonBool_pdegSeq
import Definitions.Def_PCNonBool_ppdegSeq

namespace PCNonBool

/-- **Lemma 5.7** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.28 (PDF p.31)). If FPHP(G) can be refuted in pairwise pigeon degree
`D ≥ 2`, then FPHP(G) can be refuted in pigeon degree at most `6D`.

**Formalization Note** Both refutations are in the mission's PC model (fan-in 2, lines reduced
modulo `x² - 1`, scalar-multiple axiom lines) over the same field of characteristic `≠ 2`.
Pairwise pigeon degree of a refutation is the maximum of `ppdeg` over the Qsets of its lines. -/
theorem lemma_5_7 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (D : ℝ) (hD : 2 ≤ D)
    (h : ∃ π : List (MvPolynomial (Var G) F), IsRefutation redPM (fphp G) π ∧
      (ppdegSeq G π : ℝ) ≤ D) :
    ∃ π' : List (MvPolynomial (Var G) F), IsRefutation redPM (fphp G) π' ∧
      (pdegSeq G π' : ℝ) ≤ 6 * D := by sorry

end PCNonBool
