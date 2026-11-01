-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_effective_canonical_representation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.effective_canonical_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:06:48.378653+00:00
-- url     : https://prove2.me/theorems/c6ca7012-2f6a-4622-bafe-21c64eb184ea
-- title:
--   Proposition 2: effective canonical representation
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   There are fixed normalization and canonical-reduction procedures $A,B$ and universal positive constants $K_A,K_B$. For each raw gate list $w$, $A$ returns a normalized presentation $o=H^h[c]g$, and $B$ returns actual Clifford gates $g_1,g_2$ and a canonical core $d$, with
--
--   $$[w]=[o]=g_1[d]g_2,\qquad \operatorname{cost}_A(w)+\operatorname{cost}_B(o)\le K_A(|w|+1)+K_B(\tau(c)+1)^2.$$
--
--   The bound charges the two executions separately, so normalization of a long raw input is included. The construction corresponds to Appendix D, including its recursive terminal cases.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 2, Proposition 2: effective canonical representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Proposition 2, PDF p.2, recursive construction Appendix D, pp.8--9.
The same fixed normalization and canonical phase apply to every raw gate list. -/
theorem effective_canonical_representation :
    ∃ pn pc : Program, ∃ Kn Kc : ℕ, 0 < Kn ∧ 0 < Kc ∧
      LinearNormalizes pn Kn ∧ QuadraticReduces pc Kc ∧
      ∀ w : List BsHTLetter, ∃ o : NormalOutput, ∃ c : CanonicalOutput, ∃ cn cc : ℕ,
        BsNormalized o.body ∧ BsCanonical c.body ∧
        SameGate (bsNormalValue o) (htValue w) ∧
        SameGate (canonicalValue c) (htValue w) ∧
        BsExecutes pn (htSymbols w) (normalSymbols o) cn ∧
        BsExecutes pc (normalSymbols o) (canonicalSymbols c) cc ∧
        cn + cc ≤ Kn * (w.length + 1) + Kc * (bsTCount o.body + 1) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
