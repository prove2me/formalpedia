-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P03_appendixF_finiteBlock
-- name    : QAlgorithms.Papers.Independent.Dependency50.P03.appendixF_finiteBlock
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:49:07.077778+00:00
-- url     : https://prove2.me/theorems/c4947aa2-f2e8-41d3-a39c-48e18857129a
-- title:
--   Finite-block converse with explicit continuity corrections and a common classical refinement
-- statement:
--   Let $\mathcal N:A'\to B$ be a finite-dimensional quantum channel, and let $n\ge1$. Consider any code of Appendix F: Alice initially holds one half $A_1$ of a maximally entangled state with reference $R$, and shares an independent maximally entangled state on $T_AT_B$ with Bob. Her arbitrary instrument on $A_1T_A$ outputs the channel input $A'^n$ and a classical message $M$. She sends $A'^n$ through $n$ independent uses of $\mathcal N$ and sends $M$ through a noiseless forward classical channel. Bob uses a conditional CPTP decoder on $B^nT_BM$. If its recovered state differs from the original maximally entangled target by full trace norm at most $\varepsilon$, where $0<\varepsilon<1/2$, write $\omega$ for the state before decoding, $A=RT_B$, $q=\log_2\dim R$, $c=\log_2\dim M$, and $e=\log_2\dim T_B$. Then, with all information quantities in bits,
--
--   $$
--   \begin{aligned}
--   2q&\le I(AM;B^n)_\omega+c+5q\varepsilon+3H_2(\varepsilon),\\
--   q&\le I(A\rangle B^nM)_\omega+e+4q\varepsilon+2H_2(\varepsilon).
--   \end{aligned}
--   $$
--
--   Here $H_2$ is binary entropy and $I(A\rangle B^nM)=H(B^nM)-H(AB^nM)$. There is one common refinement $X=(M,L)$, obtained by measuring the encoder's discarded Kraus environment in its defining basis, with resulting state $\sigma$, for which
--
--   $$
--   I(AM;B^n)_\omega\le I(AX;B^n)_\sigma,\qquad
--   I(A\rangle B^nM)_\omega\le I(A\rangle B^nX)_\sigma.
--   $$
--
--   These are necessary finite-block estimates for communication assisted by classical communication and entanglement. They retain the continuity terms that disappear only in the vanishing-error capacity limit.
--
--   **Formalization Note** The code and both states are constructed from finite rectangular Kraus operators and the channel. Zero-probability labels are retained, and no bound on the reference, message, or Kraus alphabet is imposed. Sizes $q,c,e$ are block quantities. The zero-dimensional registers are excluded, while dimension one and zero quantum message size are permitted.
-- source:
--   Trading classical communication, quantum communication, and entanglement in quantum Shannon theory, arXiv:0901.3038v3, PDF p. 24, Appendix F, (106)–(107), and both proof chains on PDF p.25

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P03

open scoped Matrix ComplexConjugate

/-- Appendix F, PDF pp.24–25, (106)–(107) and the two proof chains on
p.25: finite-block converse bounds, with both explicit continuity corrections.
The same computed Kraus-label refinement improves both information expressions.
Here q,c,e are block sizes, not per-use rates; hence no division by n occurs.
Source correction: the second chain's introductory '(104)' means '(105)',
and the first chain's explanatory 'A1 TB' means 'R TB', as used in its algebra
and in the final paragraph. Neither typo changes a bound. -/
theorem appendixF_finiteBlock {i o n : ℕ} (hi : 0 < i) (ho : 0 < o)
    (hn : 0 < n) (N : Superop (Fin i) (Fin o)) (hN : IsChannel N)
    (code : AssistedQuantumCode i o n) (epsilon : ℝ)
    (hepsilon_pos : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (hgood : traceNorm (decodedState N code -
      pureDensity (idealEntangled code.refDim)) ≤ epsilon) :
    (2 * quantumSize code ≤ mutualAXB (codeState N code) + classicalSize code +
      5 * quantumSize code * epsilon + 3 * binEntropy2 epsilon) ∧
    (quantumSize code ≤ coherentABX (codeState N code) + entanglementSize code +
      4 * quantumSize code * epsilon + 2 * binEntropy2 epsilon) ∧
    (mutualAXB (codeState N code) ≤ mutualAXB (refinedCodeState N code)) ∧
    (coherentABX (codeState N code) ≤ coherentABX (refinedCodeState N code)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P03

end
