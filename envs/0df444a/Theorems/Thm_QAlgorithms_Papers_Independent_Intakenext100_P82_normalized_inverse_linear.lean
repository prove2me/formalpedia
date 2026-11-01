-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_normalized_inverse_linear
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.normalized_inverse_linear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:08:47.617995+00:00
-- url     : https://prove2.me/theorems/9ba488d3-d218-4d18-9368-2c0007657398
-- title:
--   Proposition 5: normalized inverse and linear construction
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   There are a fixed symbolic procedure $A$ and a universal $K>0$ such that every normalized word $c$ yields an actual normalized word $d$ and a choice $s\in\{0,1\}$ with
--
--   $$[c]^{-1}=H[d]H(S^3)^s,\qquad \operatorname{cost}_A(c)\le K(|c|+1).$$
--
--   Here $|c|$ is syllable depth, within a fixed factor of the displayed elementary depth. The empty word is included via $H I H=I$ projectively. The proposition supplies the two inverse presentations and their linear construction.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 3, Proposition 5: normalized inverse and linear construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Proposition 5, PDF p.3. The last factor is S cubed, not G3.
No equality of T-counts is asserted; empty c is allowed. -/
theorem normalized_inverse_linear :
    ∃ p : Program, ∃ K : ℕ, 0 < K ∧
      ∀ c : List Syllable, BsNormalized c →
        ∃ d : List Syllable, ∃ hasS3 : Bool, ∃ cost : ℕ,
          BsNormalized d ∧
          SameGate (star (syllableValue c))
            (QAlgorithms.hadamard * syllableValue d * QAlgorithms.hadamard *
              (if hasS3 then QAlgorithms.phaseS ^ 3 else 1)) ∧
          BsExecutes p (syllableSymbols c)
            ([if hasS3 then 30 else 29] ++ syllableSymbols d) cost ∧
          cost ≤ K * (c.length + 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
