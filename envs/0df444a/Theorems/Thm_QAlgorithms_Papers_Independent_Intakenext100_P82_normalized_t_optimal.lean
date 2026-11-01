-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_normalized_t_optimal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.normalized_t_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:10:59.038993+00:00
-- url     : https://prove2.me/theorems/ba2572d7-f889-48bb-a29b-acbc17aa2f9f
-- title:
--   Unnumbered §V: normalization preserves the gate and minimizes T-cost
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   Let $o=H^h[c]g$ be a normalized presentation. For every competing Clifford/T word $w$ representing the same projective gate,
--
--   $$[w]=[o]\ \Longrightarrow\ \tau(c)\le\operatorname{cost}_T(w).$$
--
--   If $w$ is an $\epsilon$-approximation of a unitary target $U$, with $\epsilon>0$, the exactly equivalent presentation $o$ still satisfies $d([o],U)<\epsilon$. Thus normalization minimizes charged T-cost within an exact gate-equivalence class; optimization among distinct nearby gates is a separate problem.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 6, Unnumbered §V: normalization preserves the gate and minimizes T-cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Unnumbered §V, PDF p.6. Every normalized presentation has minimum
charged T-cost among all exact Clifford/T presentations of the same gate.
The epsilon clause preserves approximation and asserts no optimum over neighbors. -/
theorem normalized_t_optimal (o : NormalOutput) (hc : BsNormalized o.body) :
    (∀ w : List CTLetter, SameGate (ctValue w) (bsNormalValue o) →
      bsTCount o.body ≤ chargedT w) ∧
    (∀ (U : Mat), U ∈ Matrix.unitaryGroup Bool ℂ → ∀ epsilon : ℝ, 0 < epsilon →
      ∀ w : List CTLetter, SameGate (ctValue w) (bsNormalValue o) →
        gateDistance (ctValue w) U < epsilon → gateDistance (bsNormalValue o) U < epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
