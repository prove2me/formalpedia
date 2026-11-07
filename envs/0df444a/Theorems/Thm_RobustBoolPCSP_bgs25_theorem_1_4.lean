-- Prove2me | Theorems.Thm_RobustBoolPCSP_bgs25_theorem_1_4
-- name    : RobustBoolPCSP.bgs25_theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:32.468445+00:00
-- url     : https://prove2.me/theorems/7f881ea3-0002-43cd-8012-68656ce7641c
-- title:
--   [BGS25, Theorem 1.4] as cited (p.27) — a symmetric pair failing both families has a perfect integrality gap
-- statement:
--   Let $(P,Q)$ be a Boolean relation pair of arity $n$ with $P$, $Q$ symmetric and $P\subseteq Q$. Suppose some odd-arity Majority operation and some odd-arity Alternating Threshold operation fail to preserve $(P,Q)$. Then
--
--   $$\mathrm{fiPCSP}(\{(P,Q)\})\ \text{has a perfect integrality gap},$$
--
--   that is, a finite signed instance using that pair alone with a perfect basic-SDP solution and no weakly satisfying assignment.
--
--   This external result settles the case of the dichotomy in which a single pair fails both families.
--
--   Differences from the source:
--   - reading: a single pair fails both families (of the symmetric template Γ with P_j ⊆ Q_j) → a symmetric pair (P, Q) with P ⊆ Q failing some odd Maj_L and some odd AT_L; reason: the pair is a pair of the template of Theorem 2.1; the statement is taken from the citing sentence, the cited paper was not available
--   - reading: a perfect integrality gap for the basic SDP using that pair alone → a perfect integrality gap (Definition 3.1) of the one-pair template {(P, Q)}; reason: literal
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), proof of Theorem 2.1, p.27 (citing [BGS25, Theorem 1.4])

import Mathlib
import Definitions.Def_RobustBoolPCSP_SDP

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **[BGS25, Theorem 1.4]**, as cited in the proof of Theorem 2.1, p.27. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"If a single pair fails both families, the proof of [BGS25, Theorem 1.4] constructs a perfect
integrality gap for the basic SDP using that pair alone: it shows that no folded sphere coloring
satisfies the infinite instance of admissible configurations of the pair, and passes to a finite
instance by compactness, as in Lemma 4.3."

**Formalization Note.** The pair `(P, Q)` is a pair of the symmetric Boolean template of
Theorem 2.1 (symmetric relations, `P ⊆ Q`) that fails some odd Majority and some odd Alternating
Threshold; the conclusion is a perfect integrality gap (Definition 3.1) of the one-pair template
`{(P, Q)}`. -/
theorem bgs25_theorem_1_4 {n : ℕ} (P Q : Set (Fin n → Bool)) (hP : IsSymmetricRel P)
    (hQ : IsSymmetricRel Q) (hPQ : P ⊆ Q)
    (hMaj : ∃ L : ℕ, Odd L ∧ ¬ PolOf P Q (Maj L))
    (hAT : ∃ L : ℕ, Odd L ∧ ¬ PolOf P Q (AT L)) :
    HasPerfectGap (Template.single P Q) := by sorry

end RobustBoolPCSP
