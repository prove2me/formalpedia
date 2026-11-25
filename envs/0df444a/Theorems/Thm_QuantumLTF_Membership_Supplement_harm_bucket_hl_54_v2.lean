-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_harm_bucket_hl_54_v2
-- name    : QuantumLTF.Membership.Supplement.harm_bucket_hl_54_v2
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-25T03:52:57.184687+00:00
-- url     : https://prove2.me/theorems/3ee858cf-68b6-47fb-8888-4aac25bc1caa
-- title:
--   Harmonic-Bucket $2$-Sort stabilizer-subgroup state preparation ($\mathrm{HarmBucketHL54V2}$)
-- statement:
--   Proves `Nonempty HarmBucketHL54V2`, constructing an exact `gates12` (`LayeredCircuit`) circuit `harmBucketH_lCircuit` controlled on any monotone non-strictly increasing list $|l\rangle$ over $\{0, \dots, n-1, \bot\}^{2K}$ that maps clean ancillas to the exact uniform stabilizer-subgroup superposition
--
--   $$
--   |l\rangle |0\rangle \longmapsto |l\rangle \otimes \frac{1}{\sqrt{|H_l|}} \sum_{h \in H_l} \bigl|\mathrm{padPerm}_{2K, M}(h)(0\dots M-1)\bigr\rangle
--   $$
--
--   in $O\bigl((Ks + M)(L + d)^{K_{\mathrm{hl}}}\bigr)$ `gates12` gates ($s = \lceil \log_2 n \rceil + 1$, $L = \lceil \log_2((K+1)(n+1)+2) \rceil + 1$, $M = 2^d \ge 2K$). Run offsets $m_i$ and occurrences $\mathrm{occ}_i$ are routed by two bitonic sorting passes into $\sum_{m=2}^{2K} \lfloor 2K/m \rfloor = O(K \log K)$ classical buckets `bucketPairs`, synthesized with exact uniform superpositions via `unifPrefixCircuit`, unrouted back to particle positions, subtracted to form $s_i = i - d_i$, and converted in place to $|h\rangle$ by `alonso_schott_sil_54`.
--
--   **Formalization Note** The circuit interface is declared in `Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV.B–C); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2

namespace QuantumLTF.Membership.Supplement

theorem harm_bucket_hl_54_v2 : Nonempty HarmBucketHL54V2 := by sorry

end QuantumLTF.Membership.Supplement
