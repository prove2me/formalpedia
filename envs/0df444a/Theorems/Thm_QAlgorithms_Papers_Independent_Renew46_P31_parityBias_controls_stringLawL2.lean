-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P31_parityBias_controls_stringLawL2
-- name    : QAlgorithms.Papers.Independent.Renew46.P31.parityBias_controls_stringLawL2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:03:26.228314+00:00
-- url     : https://prove2.me/theorems/ae853915-a56a-44e0-8eb8-b3e2dde67c02
-- title:
--   All parity-bit biases control the Euclidean distance of string laws
-- statement:
--   Let $m\ge 0$ be an integer, and let $Z$ and $Z_{\mathrm{ideal}}$ be random strings in $\{0,1\}^m$ with probability laws $P$ and $P_{\mathrm{ideal}}$. Let $\varepsilon\ge 0$. For a mask $X\in\{0,1\}^m$, write $X\otimes Z=\bigoplus_{j=1}^m X_j Z_j$ for the parity of the selected bits. Suppose that for every mask $X$,
--
--   $$
--   \left|\Pr[X\otimes Z=0]-\Pr[X\otimes Z_{\mathrm{ideal}}=0]\right|\le\varepsilon.
--   $$
--
--   Then
--
--   $$
--   \left(\sum_{z\in\{0,1\}^m}\left|P(z)-P_{\mathrm{ideal}}(z)\right|^2\right)^{1/2}\le 2\varepsilon.
--   $$
--
--   Thus uniform control of all parity tests controls the Euclidean distance of the full string distributions. The sum uses ordinary counting weights. The assertion includes the empty string at $m=0$.
--
--   **Formalization Note** Both laws are normalized probability mass functions. The real Euclidean vector has coordinates $P(z)-P_{\mathrm{ideal}}(z)$; zero is the Boolean value `false`.
-- source:
--   General Security Definition and Composability for Quantum & Classical Protocols, arXiv:quant-ph/0409062v2, PDF p. 5, §2.4, unnumbered parity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P31

namespace QAlgorithms.Papers.Independent.Renew46.P31

/-- Ben-Or and Mayers, arXiv:quant-ph/0409062v2, Section 2.4, PDF page 5:
if every parity bit has zero-outcome probability differing by at most `epsilon`,
then the Euclidean L2 distance between the two normalized string laws is at most
`2 * epsilon`. The masks range over every `m`-bit string. The ordinary Euclidean
norm is unweighted; it is neither total variation nor a normalized counting norm.
The empty string (`m = 0`) is allowed. -/
theorem parityBias_controls_stringLawL2
    (m : ℕ) (P Pideal : PMF (QAlgorithms.Qubits m))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hparity : ∀ X : QAlgorithms.Qubits m,
      |(P.map (QAlgorithms.dotBits X) false).toReal -
        (Pideal.map (QAlgorithms.dotBits X) false).toReal| ≤ epsilon) :
    ‖(WithLp.toLp 2 (fun z : QAlgorithms.Qubits m =>
      (P z).toReal - (Pideal z).toReal) :
        EuclideanSpace ℝ (QAlgorithms.Qubits m))‖ ≤ 2 * epsilon := by sorry

end QAlgorithms.Papers.Independent.Renew46.P31
