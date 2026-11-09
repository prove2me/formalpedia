-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_6_1
-- name    : TreeEquivalenceHORS.Equivalence.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:25.156525+00:00
-- url     : https://prove2.me/theorems/eb811d8d-266f-44d0-a8a8-dadfffe0fc7f
-- title:
--   Lemma 6.1 (Head adequacy): $[\![t]\!]_{\eta^*}=1\iff\exists a,\vec u\ t\Downarrow_G a(\vec u)$
-- statement:
--   For a well-formed scheme $G$ (of any finite order, not necessarily safe or productive) and a closed ground term $t$,
--   $$[\![t]\!]_{\eta^*}=1\iff\exists a,\vec u\ \ t\Downarrow_G a(\vec u),$$
--   where $\eta^*=\Phi_G^{B}(\eta_0)$ is the least fixed point of the finite monotone semantics.
--
--   This decides head convergence, which a search over unfolding budgets alone can only semidecide.
--
--   Differences from the source:
--   - encoding: finite posets D_σ of monotone maps; environments in the finite product E_G → enumerated finite tables `enum σ` of type `List SVal` (Section 6.2), application by table lookup, environments as lists indexed by nonterminals; reason: the representation of Section 6.2; the tables are exactly the monotone maps
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 6.1, printed p. 23 / PDF p. 25

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 6.1 (Head adequacy)** (printed p. 23 / PDF p. 25). For a well-formed scheme `G` and a
closed ground term `t`, `⟦t⟧_{η*} = 1 ⟺ ∃ a, u⃗, t ⇓_G a(u⃗)`. -/
theorem lemma_6_1 (G : HORS) (hG : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o) :
    G.den [] G.etaStar [] t = .bit true ↔ ∃ (c : ℕ) (us : List Tm), G.HeadConv t c us := by sorry

end TreeEquivalenceHORS.Equivalence
