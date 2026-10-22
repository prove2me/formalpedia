-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_commitment_strongBinding
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.commitment_strongBinding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:24:06.48297+00:00
-- url     : https://prove2.me/theorems/29b8274e-9947-409f-b5ca-0d78eda9b01c
-- title:
--   Theorem 5.2: strong binding of concrete commitment
-- statement:
--   Let $q(n)$ be nonnegative integers with positive linear slack below $n/4$: there are $a>0,N$ such that $an\le n/4-q(n)$ for all $n\ge N$. There is a nonnegative negligible function $\varepsilon(n)$, uniform over all dishonest committers, such that the concrete four-step commitment of Figure 2 has perfect honest correctness and is strongly $\varepsilon(n)$-binding. For every attack there is a single classical kernel $P(B'\mid V,Z)$, chosen before all opening strategies, such that on each supported branch $B'=b$,
--   $$\Pr[\text{verifier accepts an opening to }1-b\mid B'=b]\le\varepsilon(n).$$
--   Here $V$ is the verifier's classical preparation record, $Z$ is the committer's full classical record, and its residual quantum register has at most $q(n)$ qubits at the start of opening. The verifier checks every matching-basis bit. All opening strategies retain access to $Z$ and the residual quantum system. This is Definition 5.1, rather than only the weak sum bound.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 12, Theorem 5.2: strong binding of concrete commitment

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Theorem 5.2, pp.12-13: negligible STRONG binding, with the memory bound
only at the START OF OPENING. Unlimited classical storage and arbitrary opening
POVMs are universally quantified; the binding kernel precedes those POVMs. -/
theorem commitment_strongBinding (q : ℕ → ℕ)
    (hslack : ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n ≥ N, a*n ≤ (n:ℝ)/4-q n) :
    ∃ epsilon : ℕ → ℝ, Negligible epsilon ∧ ∀ n,
      HonestCommitCorrect n ∧
      ∀ (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] (A : StorageMap n (q n) Z),
        StronglyBinding (commitmentBlocks A) commitmentAccept (epsilon n) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
