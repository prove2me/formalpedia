-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_theorem_1_1
-- name    : UnequalHuffman.NPC.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:23.661395+00:00
-- url     : https://prove2.me/theorems/e3228ca4-ade8-4bb8-8849-27c9be1c92e0
-- title:
--   Theorem 1.1 — Binary prefix coding with unequal letter costs is NP-complete, even for costs (M, M + 1) with M in the input
-- statement:
--   **Binary Prefix Coding with Unequal Letter Costs.** Given positive integer frequencies $w_1,\dots,w_N$ with $N \ge 2$, positive integer letter costs $c_0 < c_1$ and a nonnegative integer threshold $K$, all in binary, decide whether some binary prefix code $C$ has
--   $$\mathrm{cost}_{c_0,c_1}(C) = \sum_{i=1}^N w_i\,(c_0|C_i|_0 + c_1|C_i|_1) \le K.$$
--
--   **Theorem 1.1.** This problem (`huffLang`) is NP-complete, and so is its restriction to letter costs $(c_0, c_1) = (M, M+1)$ with the positive integer $M$ supplied as part of the instance (`huffConsecLang`):
--   $$\mathtt{huffLang} \in \mathrm{NPC} \quad\text{and}\quad \mathtt{huffConsecLang} \in \mathrm{NPC}.$$
--   NP-completeness is `CookPvsNP.NPComplete`: membership in NP and a polynomial-time many-one reduction from every NP language over every finite nonempty alphabet.
--
--   Source (p. 5): "Theorem 1.1. Deciding whether there is a binary prefix code of cost at most $K$ is NP-complete, even when $(c_0, c_1) = (M, M+1)$ for a positive integer $M$ supplied as part of the instance. All frequencies, letter costs, and the threshold are encoded in binary."
--
--   Differences from the source:
--   - encoding: NP-complete → CookPvsNP.NPComplete over the alphabet BSym: in NP, and every NP language over every finite nonempty alphabet is polynomial-time many-one reducible to it; reason: the published definition (Cook's one-tape machines)
--   - encoding: an instance (w_1, …, w_N; c0 < c1; K) with every number in binary → instCode w c0 c1 K = encNats ([c0, c1, K] ++ w); strings that encode no well-formed instance (N < 2, some w_i = 0, c0 = 0, c0 ≥ c1, malformed) are not in the language; reason: the published binary number code; N is determined by the code
--   - encoding: even when (c0, c1) = (M, M + 1), M a positive integer supplied as part of the instance → huffConsecLang: the strings instCode w M (M + 1) K of well-formed yes-instances; reason: the same instance code with c1 = M + 1 written out, M read from the input
--   - encoding: binary prefix code C = (C_1, …, C_N) → C : Fin N → List Bool with FuchsThesis.Coding.IsInstantaneous; false = letter 0 (cost c0), true = letter 1 (cost c1); reason: the published prefix-code definition; any lengths and tree shapes
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 5, Theorem 1.1 (proof §4.4, p. 35)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Language

open CookPvsNP

namespace UnequalHuffman.NPC

/-- Theorem 1.1 (p. 5): Binary Prefix Coding with Unequal Letter Costs (frequencies, letter costs
and threshold in binary) is NP-complete, and so is its restriction to letter costs
`(c₀, c₁) = (M, M + 1)` with the positive integer `M` read from the instance. -/
theorem theorem_1_1 : NPComplete huffLang ∧ NPComplete huffConsecLang := by sorry

end UnequalHuffman.NPC
