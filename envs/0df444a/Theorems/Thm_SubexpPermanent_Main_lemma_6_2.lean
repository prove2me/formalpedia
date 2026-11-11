-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_6_2
-- name    : SubexpPermanent.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:03:08.412412+00:00
-- url     : https://prove2.me/theorems/7f8128f6-8576-4ef4-981f-cda0d2731267
-- title:
--   Lemma 6.2 — $\mathrm{OPT}_A(a)$ is finite and attained on $D_a$ for every real $a$
-- statement:
--   Let $A$ be a nonnegative real $n\times n$ matrix with $\operatorname{per}(A)>0$, with $\Phi_A$, $D_a$ and $\mathrm{OPT}_A(a)=\min_{y\in D_a}\Phi_A(y)$ as in §6. For every $a\in\mathbb R$, the value $\mathrm{OPT}_A(a)$ is finite and equals $\Phi_A(y)$ for some $y\in D_a$:
--   $$\exists\,y\in D_a:\quad \Phi_A(y)\le\Phi_A(y')\ \ \forall y'\in D_a,\qquad \Phi_A(y)=\mathrm{OPT}_A(a).$$
--   The lemma justifies writing $\min$ in (5), and it supplies the minimizers used in Lemmas 6.3 and 6.4.
--
--   Differences from the source:
--
--   - encoding: vectors in ℝ^E indexed by the edges of E → functions on the subtype Edges A of pairs (i, j) in E; reason: the same space with the same coordinates
--   - encoding: OPT_A(a) = min over D_a, finite → OPT A a is the real infimum ⨅ over D_a; the conclusion is a y ∈ D_a minimizing Φ_A on D_a with Φ_A(y) = OPT A a; reason: an attained infimum is finite and equals the minimum
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 21, Lemma 6.2

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Objective

namespace SubexpPermanent.Main

/-- Lemma 6.2 (existence of a minimizer), p. 21. -/
theorem lemma_6_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hper : 0 < A.permanent) (a : ℝ) :
    ∃ y ∈ budgetSet A a, IsMinOn (Phi A) (budgetSet A a) y ∧ Phi A y = OPT A a := by sorry

end SubexpPermanent.Main
