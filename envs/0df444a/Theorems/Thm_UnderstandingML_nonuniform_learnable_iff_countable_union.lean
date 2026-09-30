-- Prove2me | Theorems.Thm_UnderstandingML_nonuniform_learnable_iff_countable_union
-- name    : UnderstandingML.nonuniform_learnable_iff_countable_union
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:47:14.507121+00:00
-- url     : https://prove2.me/theorems/c709cbcd-f1fe-439c-9fcd-de12b6ba0401
-- title:
--   Theorem 7.2: a class of binary classifiers is nonuniformly learnable iff it is a countable union of agnostic PAC learnable classes
-- statement:
--   **Theorem 7.2.** A hypothesis class $H$ of binary classifiers is nonuniformly learnable if and only if it is a countable union of agnostic PAC learnable hypothesis classes.
--
--   Formally: for a class of measurable hypotheses over a domain with measurable singletons, every subclass of which is pointwise separable (the measurability assumption of Remark 3.1 needed by the fundamental theorem; automatic over a countable domain), `NonuniformLearnable loss01 H` holds iff there are classes $H_n$ with $\bigcup_n H_n = H$ and each $H_n$ agnostic PAC learnable.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.1.1 pp. 84-85, Theorem 7.2 with its proof (via Theorems 6.7 and 7.3)

import Definitions.Def_UnderstandingML_Nonuniform

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 7.2** (p. 84). A hypothesis class `H` of binary classifiers is nonuniformly
learnable if and only if it is a countable union of agnostic PAC learnable hypothesis classes.
The domain has measurable singletons, the hypotheses are measurable, and every subclass of `H`
is pointwise separable (the measurability assumption of Remark 3.1, which the fundamental
theorem needs; it holds for every class over a countable domain). -/
theorem nonuniform_learnable_iff_countable_union {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (H : Set (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    (hsep : ∀ H' ⊆ H, PointwiseSeparable H') :
    NonuniformLearnable loss01 H ↔
      ∃ Hn : ℕ → Set (X → Bool), (⋃ n, Hn n) = H ∧
        ∀ n, AgnosticPACLearnable loss01 (Hn n) := by sorry

end UnderstandingML
