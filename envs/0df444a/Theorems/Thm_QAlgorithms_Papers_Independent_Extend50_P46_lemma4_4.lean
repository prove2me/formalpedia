-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P46_lemma4_4
-- name    : QAlgorithms.Papers.Independent.Extend50.P46.lemma4_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:07:37.023257+00:00
-- url     : https://prove2.me/theorems/cdd0f11a-109f-429e-84a5-b602b2b7d7b7
-- title:
--   Discovering the significant entries of a sparse Pauli transfer matrix
-- statement:
--   The unknown channel is an arbitrary complex-linear CPTP map on $n$ qubits. Choi access supplies independent copies of the normalized reference-first state $J(\mathcal N)=(\mathrm{id}\otimes\mathcal N)(|\Omega\rangle\langle\Omega|)$. The algorithm is a joint POVM on exactly its stated number of copies, chosen before the channel. Accuracy means simultaneous absolute error under its actual Born law. All constants, and all exponents hidden in $\widetilde O$, are uniform before the channel, dimension, basis and accuracy parameters. Assume $\varepsilon>0$ and $0<\delta<1$.
--
--   Assume the unknown PTM has at most $s$ nonzero entries, without supplied support. Using
--
--   $$m=O\!\left(\frac{n+\log(1/\delta)}{\varepsilon^4}\right),$$
--
--   the learner returns a finite list of distinct locations and estimates such that, simultaneously with probability at least $1-\delta$: omitted true entries have magnitude at most $\varepsilon$; listed true entries have magnitude strictly greater than $\varepsilon/6$; the list has length at most $s$; and every listed estimate has error at most $\varepsilon$.
--
--   The list is computed by retaining entries whose preliminary estimated magnitude exceeds $\varepsilon/2$. This provides support discovery rather than support advice.
-- source:
--   Learning Quantum Processes and Hamiltonians via the Pauli Transfer Matrix, arXiv:2212.04471v2, PDF p. 23, Lemma 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P46

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P46

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.23-24, Lemma 4.4: support discovery and all four list guarantees.
The list is the finite filter at the strict eps/2 cutoff, with each retained value read from r. -/
theorem lemma4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ n s : ℕ, ∀ eps delta : ℝ,
      0 < eps → 0 < delta → delta < 1 →
      ∃ P : ChoiLearner n (Matrix (ErrorMitigation.PauliIndex n) (ErrorMitigation.PauliIndex n) ℝ),
        (P.copies : ℝ) ≤ C * (n + Real.log delta⁻¹) / eps^4 ∧
        ∀ N : {F : (Matrix (Qubits n) (Qubits n) ℂ) →ₗ[ℂ] (Matrix (Qubits n) (Qubits n) ℂ) // IsChannel F}, supportCount (fun p : ErrorMitigation.PauliIndex n × ErrorMitigation.PauliIndex n => ptm N p.1 p.2) ≤ s →

          1 - delta ≤ choiReportEventProbability P N {r | sparseListGood r (ptm N) eps s} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P46

end
