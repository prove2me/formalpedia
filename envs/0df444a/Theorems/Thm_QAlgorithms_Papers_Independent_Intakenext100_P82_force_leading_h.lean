-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_force_leading_h
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.force_leading_h
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:09:42.831632+00:00
-- url     : https://prove2.me/theorems/41039715-dfca-4933-af32-10c25b7f661b
-- title:
--   Lemma 1 (Appendix D): force a leading H without changing the body T-count
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   There are a fixed symbolic rewrite procedure $A$ and a universal $K>0$ such that every normalized word $c$ yields a normalized word $d$ and an actual $g\in C$ with
--
--   $$[SH\,TH\,c]=H[SH\,TH\,d]g,\qquad \tau(d)=\tau(c),\qquad \operatorname{cost}_A(c)\le K(\tau(c)+1).$$
--
--   The actual output retains the external $H$, the initial $SH\,TH$, the body and the Clifford terminal. This forces the required leading $H$ without changing the sub-body T-count, including when the sub-body is empty.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 8, Lemma 1 (Appendix D): force a leading H without changing the body T-count

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Lemma 1 of Appendix D, PDF pp.8--9. The entire output still begins
with external H followed by SH.TH; only the sub-body is replaced. -/
theorem force_leading_h :
    ∃ p : Program, ∃ K : ℕ, 0 < K ∧
      ∀ c : List Syllable, BsNormalized c →
        ∃ d : List Syllable, ∃ g : Fin 24, ∃ cost : ℕ,
          BsNormalized d ∧ bsTCount d = bsTCount c ∧
          SameGate (syllableValue (.sh :: .th :: c))
            (QAlgorithms.hadamard * syllableValue (.sh :: .th :: d) * cliffordMatrix g) ∧
          BsExecutes p (syllableSymbols (.sh :: .th :: c))
            (normalSymbols ⟨true, .sh :: .th :: d, g⟩) cost ∧
          cost ≤ K * (bsTCount c + 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
