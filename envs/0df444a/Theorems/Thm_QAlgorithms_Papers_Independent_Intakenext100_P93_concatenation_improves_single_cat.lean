-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P93_concatenation_improves_single_cat
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P93.concatenation_improves_single_cat
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:38:06.447829+00:00
-- url     : https://prove2.me/theorems/71f1e8c4-bcaa-4796-821d-09637576da73
-- title:
--   Concatenated Repetition Codes: strict threshold advantage over every single cat
-- statement:
--   Consider independent depolarizing noise with total nonidentity probability $p$ and $p_x=p_y=p_z=p/3$. For an inner length $A\in\{3,5\}$ and a positive outer length $B$, construct the encoder
--
--   $$
--   V_{A,B}=V_{Z,A}^{\otimes B}V_{X,B},\qquad V_{X,B}=H^{\otimes B}V_{Z,B}H,
--   $$
--
--   where $V_{Z,j}|c\rangle=|c\rangle^{\otimes j}$. Apply the physical channel and the inverse two-level decoder, measuring and retaining every inner Z syndrome and the outer X syndrome. Let $R_{A,B}(p)$ be the coherent information of this actual flagged Bell output divided by $AB$, and let $R_m(p)$ be the corresponding single-cat rate. For any such rate function define its low-noise positivity threshold by $t(R)=\sup(\{0\}\cup\{p\in[0,3/4]:R(p)>0\})$. Then
--
--   $$
--   \exists A\in\{3,5\},\ B\ge1\quad\forall m\ge1:\qquad t(R_m)<t(R_{A,B}).
--   $$
--
--   This is a strict zero-rate threshold advantage of some fixed concatenation over every single cat. It asserts neither pointwise superiority at every noise value nor optimality among arbitrary quantum codes; no rounded numerical optimizer is used. For these same fixed lengths and every $p\in[0,3/4]$ with $R_{A,B}(p)\ge0$, that rate is achievable by tensor copies of the constructed two-level inner encoder followed by an additive outer stabilizer encoder and a CPTP decoder. For every error $\epsilon>0$ and rate slack $\delta>0$, all sufficiently large positive outer blocklengths $n$ admit a code with $l\ge(R_{A,B}(p)-\delta)ABn$ logical qubits and both entanglement fidelity and every normalized pure-input transmission fidelity at least $1-\epsilon$. The encoder and decoder are chosen before the unknown input.
-- source:
--   Degenerate Quantum Codes for Pauli Channels, arXiv:quant-ph/0604107v2, PDF p. 3, Concatenated Repetition Codes: strict threshold advantage over every single cat

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P93

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P93

open QAlgorithms

open scoped BigOperators ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Smolin, PDF p.3, Concatenated Repetition Codes / Fig.2:
a fixed 3- or 5-qubit Z-inner/X-outer concatenation has a strictly larger
zero-rate noise threshold than every single cat. Its nonnegative yield is
operationally achievable by the Eq.(5) outer-stabilizer construction.
Here a+1 is the inner length; no rounded optimum is asserted. -/
theorem concatenation_improves_single_cat :
    ∃ a b : ℕ, (a = 2 ∨ a = 4) ∧
      (∀ p : ℝ, 0 ≤ p → p ≤ 3 / 4 → 0 ≤ concatenatedRate a b p →
        ConcatenatedAchievable a b p (concatenatedRate a b p)) ∧
      ∀ k : ℕ,
        noiseThreshold (fun p => catRate k (p / 3) (p / 3) (p / 3)) <
          noiseThreshold (concatenatedRate a b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P93

end
