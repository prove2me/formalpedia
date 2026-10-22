-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_worstCaseErasureGap
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.worstCaseErasureGap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:01:10.228268+00:00
-- url     : https://prove2.me/theorems/2d6832dd-55ff-4417-be6e-0e8c2a999b50
-- title:
--   Asymptotic erasure capacity versus perfect correction of every pattern
-- statement:
--   For a finite-dimensional memoryless quantum channel, write $Q$ for unassisted quantum transmission capacity, $Q_2$ for quantum transmission capacity with free two-way classical communication, and $C$ for unassisted classical capacity. Quantum rates are in qubits per forward use and classical rates are in bits per forward use. Encoders and decoders are arbitrary CPTP operations, with no efficiency restriction. Quantum reliability is squared pure-state fidelity uniformly over every normalized unknown logical input. Classical reliability is worst-message decoding error. A code is chosen before its input; for every rate below capacity and every positive error tolerance a positive block length and a code of strictly greater rate exist. Independent uses act on arbitrary entangled blocks. Two-way protocols have arbitrary finite adaptive classical rounds and finite quantum memories, with no initial shared entanglement. Fix $1/3<\epsilon<1/2$ and let $\mathcal E_\epsilon$ be the qubit quantum erasure channel. Its classical capacity is positive. There is an integer $N\ge1$, depending on $\epsilon$, such that for every $n\ge N$ there is no nontrivial fixed quantum code subspace of $n$ qubits that perfectly corrects every pattern of $\lfloor n\epsilon\rfloor$ erasures:
--
--   $$C(\mathcal E_\epsilon)>0,\qquad \exists N\ge1\ \forall n\ge N\ \forall k\ge2\ \forall V:\mathbb C^k\hookrightarrow(\mathbb C^2)^{\otimes n},\quad \neg\operatorname{CorrectsAll}_{\lfloor n\epsilon\rfloor}(V).$$
--
--   Here $V$ is an isometric encoding of one fixed subspace. Perfect correction means that for each erased set of the stated size there exists a CPTP recovery, permitted to depend on that set, which recovers every logical density matrix exactly. The restriction $k\ge2$ excludes codes carrying no quantum information.
--
--   This comparison separates large-block worst-pattern perfect correction from the source’s vanishing-error notion of capacity. The printed symbol is $C$ and is retained.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 4, Unnumbered comparison and Fig. 2(a)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF pp.3--4 and Fig.2(a): retain the printed C.
The all-pattern impossibility is asymptotic, with floor(n*p) as the integer
convention. Nontrivial subspaces (dimension at least two) exclude the zero-qubit
code. The erased-set-dependent decoder is allowed by CorrectsEveryPattern. -/
theorem worstCaseErasureGap (p : ℝ) (hp0 : (1 : ℝ)/3 < p) (hp1 : p < (1 : ℝ)/2) :
    0 < worstMessageCapacity (QAlgorithms.Papers.Independent.Dependency50.P09.erasureFin 2 p) ∧
    ∃ threshold : ℕ, 0 < threshold ∧ ∀ n : ℕ, threshold ≤ n →
      ∀ k : ℕ, 2 ≤ k → ∀ V : Matrix (Qubits n) (Fin k) ℂ,
        ¬ CorrectsEveryPattern V ⌊(n : ℝ)*p⌋₊ := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
