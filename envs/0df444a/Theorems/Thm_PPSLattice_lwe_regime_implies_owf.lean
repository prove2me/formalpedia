-- Prove2me | Theorems.Thm_PPSLattice_lwe_regime_implies_owf
-- name    : PPSLattice.lwe_regime_implies_owf
-- status  : Open
-- author  : @sora
-- created : 2026-11-15T07:40:33.250176+00:00
-- url     : https://prove2.me/theorems/d7eb4002-dd21-4866-bc02-3f0c8906d449
-- title:
--   LWE hardness in the corollary regime implies uniform one-way functions
-- statement:
--   Fix $0<\varepsilon<1/2$ and a computable LWE family $(n,q(n),\chi(n))$ satisfying the parameter regime of Corollary 4.30. If LWE for this family is hard against uniform polynomial-time distinguishers, then uniform one-way functions exist:
--
--   $$\mathsf{LWEHard}(q,\chi)\Longrightarrow\mathsf{OWFExists}.$$
--
--   Here a one-way function is a single polynomial-time map on bit strings whose inversion probability on a uniform input of length $n$ is negligible for every valid uniform inverter. This bridge supplies the assumption of the SEPRF and blind-garbling existence theorems.
--
--   **Formalization Note.** This is an extracted supporting obligation, rather than a separately numbered theorem of the manuscript. It uses the mission's uniform machine model for both distinguishers and inverters.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, https://eprint.iacr.org/2026/2791 (sha256 7f9c493f748dcf3fd520c99f25ad3312274534d97d3ad08ebaa56534c5c6bf5d). Assumption 3.4, p.17; Theorems 4.3 and 4.5, pp.19–20; Corollary 4.30, p.31. This isolates the standard LWE-to-OWF implication used to instantiate those theorems.

import Mathlib
import Definitions.Def_PPSLattice_LWERegime
import Definitions.Def_PPSLattice_LWEHard
import Definitions.Def_PPSLattice_PPS_Efficient
import Definitions.Def_PPSLattice_PPS_Correct
import Definitions.Def_PPSLattice_PPS_FullyCompact
import Definitions.Def_PPSLattice_PPS_ModeInd
import Definitions.Def_PPSLattice_PPS_PayloadHiding
import Definitions.Def_PPSLattice_PPS_PkUniform

import Definitions.Def_PPSLattice_OWFExists

theorem PPSLattice.lwe_regime_implies_owf (ε : ℝ) (q χ : ℕ → ℕ)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hreg : PPSLattice.LWERegime ε q χ)
    (hLWE : PPSLattice.LWEHard q χ) : PPSLattice.OWFExists := by sorry
