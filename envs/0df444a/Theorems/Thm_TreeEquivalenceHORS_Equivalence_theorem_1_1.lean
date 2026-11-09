-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_theorem_1_1
-- name    : TreeEquivalenceHORS.Equivalence.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:04.989562+00:00
-- url     : https://prove2.me/theorems/124040a3-d746-4bdc-83a3-71c48412e3e8
-- title:
--   Theorem 1.1 (Tree equivalence): tree equivalence of HORS is undecidable and $\Pi^0_1$-complete, also for safe productive order-four schemes over $\Sigma_2$
-- statement:
--   Tree equivalence of deterministic higher-order recursion schemes is undecidable and, more precisely, $\Pi^0_1$-complete (co-c.e.-complete) under total computable many-one reductions. This remains true when both schemes are required simultaneously to be safe and productive, to have order at most four, and to use the fixed ranked alphabet $\Sigma_2=\{e:0,d:2\}$.
--
--   Precisely, each of the four languages of Section 3,
--   $$\mathrm{Eq}_{\mathrm{HORS}},\quad\mathrm{Eq}_{4,\Sigma_2},\quad\mathrm{Eq}^{\mathrm{prod}}_{4,\Sigma_2},\quad\mathrm{Eq}^{\mathrm{safe,prod}}_{4,\Sigma_2},$$
--   is co-c.e., every co-c.e. predicate on $\mathbb N$ many-one reduces to it by a total computable function, and it is not computable.
--
--   The general language allows arbitrary alphabets, arbitrary finite orders and nonproductive schemes. The restricted languages impose their conditions on both schemes, and productivity is part of membership.
--
--   Differences from the source:
--   - reading: "Tree equivalence … is … Π⁰₁-complete …; this remains true when both schemes are required simultaneously to be safe and productive, to have order at most four, and to use Σ₂" → the conclusion stated for each of the four languages Eq_HORS, Eq_{4,Σ₂}, Eq^prod_{4,Σ₂}, Eq^{safe,prod}_{4,Σ₂} of Section 3; reason: these are the languages the paper defines for the headline and proves the theorem for (Sections 5.6, 6.4)
--   - encoding: Π⁰₁-complete under total computable many-one reductions; undecidable → `CoCEComplete P` (`REPred` of the complement, and `ManyOneReducible A P` for every co-c.e. A) and `¬ ComputablePred P`; reason: Mathlib's conventional computability notions on ℕ
--   - encoding: standard computable injective encodings of finite syntax by natural numbers, with total computable decoders that return syntax or reject → the derived `Encodable` instances of `Ty`, `Tm`, `HORS`, `Instr` (and their products, lists, options); a code on which `Encodable.decode` returns `none` is malformed; reason: the derived encoding is injective with a total, structurally recursive decoder; computability classes of predicates on ℕ do not depend on which such encoding is fixed
--   - encoding: Σ₀ = {z:0, a:1, b:3}, Σ₂ = {e:0, d:2} → `sigma0 = [0, 1, 3]` (terminals 0 = z, 1 = a, 2 = b) and `sigma2 = [0, 2]` (0 = e, 1 = d); reason: a ranked alphabet is its list of arities, terminals named by position
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Theorem 1.1, printed p. 1 / PDF p. 3; languages Section 3, printed p. 11 / PDF p. 13

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages

namespace TreeEquivalenceHORS.Equivalence

/-- **Theorem 1.1 (Tree equivalence)** (printed p. 1 / PDF p. 3). Tree equivalence of deterministic
higher-order recursion schemes is undecidable and `Π⁰₁`-complete (co-c.e.-complete) under total
computable many-one reductions; this remains true when both schemes are required simultaneously
to be safe and productive, to have order at most four, and to use the alphabet `Σ₂ = {e : 0, d : 2}`.
Stated for each of the four languages of Section 3: `Eq_HORS`, `Eq_{4,Σ₂}`, `Eq^prod_{4,Σ₂}` and
`Eq^{safe,prod}_{4,Σ₂}`. -/
theorem theorem_1_1 :
    (CoCEComplete EqHORS ∧ ¬ ComputablePred EqHORS) ∧
    (CoCEComplete Eq4Sigma2 ∧ ¬ ComputablePred Eq4Sigma2) ∧
    (CoCEComplete Eq4Sigma2Prod ∧ ¬ ComputablePred Eq4Sigma2Prod) ∧
    (CoCEComplete Eq4Sigma2SafeProd ∧ ¬ ComputablePred Eq4Sigma2SafeProd) := by sorry

end TreeEquivalenceHORS.Equivalence
