-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_classical_entanglement_region
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.classical_entanglement_region
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:12:10.865347+00:00
-- url     : https://prove2.me/theorems/c0d57b39-2f39-4526-aef1-2f2b8777a769
-- title:
--   Blind compression using classical messages and entanglement
-- statement:
--   Let $\{p(x),|\psi_x\rangle^A\}$ be a countably supported pure-state ensemble with positive normalized probabilities on a finite-dimensional complex system $A$. Let $Y$ be its canonical orthogonal irreducible-component label, obtainable locally without disturbance. Entropies are in bits.
--
--   Alice and Bob initially share a maximally entangled state of local dimension $K_n$. Alice uses a finite trace-nonincreasing CP instrument, with trace-preserving sum, acting on $A^n$ and her Bell half and retaining the component label $Y^n$. She sends only the instrument's classical outcome from an alphabet of size $m_n$; Bob applies a message-conditioned CPTP decoder to his Bell half. There is no quantum message and no upper cap on $m_n$. A real pair $(c,e)$ is achievable when codes for every positive $n$ have average joint $AY$ root fidelity tending to one, $\log_2 m_n/n\to c$, and $\log_2 K_n/n\to e$.
--
--   The exact achievable region is
--   $$ (c,e)\text{ achievable}\quad\Longleftrightarrow\quad c\ge2S(A)-S(Y),\qquad e\ge S(A)-S(Y). $$
--
--   This is the modified classical-communication model of the paragraph preceding Theorem 8, with $c$ measured in cbits per source letter.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 5, Theorem 8

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Theorem 8, PDF p.5: exact classical-message/entanglement region in the
modified blind-source model. Y is the canonical locally extracted label.
C in the source formula denotes cbits, not the side Hilbert space. -/
theorem classical_entanglement_region [Countable X] (s : ProductPureSource X A Unit)
    (hs : s.Valid) (c e : ℝ) :
    BlindClassicalAchievable s c e ↔
      2 * s.entropyA - s.entropyY ≤ c ∧ s.entropyA - s.entropyY ≤ e := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
