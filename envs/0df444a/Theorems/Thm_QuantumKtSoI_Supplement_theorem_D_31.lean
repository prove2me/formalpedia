-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_31
-- name    : QuantumKtSoI.Supplement.theorem_D_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:51:53.388647+00:00
-- url     : https://prove2.me/theorems/c3f57ea4-ae42-4d83-9e9d-e6181ad4fec8
-- title:
--   Theorem D.31, p.181 — a quasi-linear universal machine exists
-- statement:
--   There is a quasi-linear universal machine $U_{\mathrm{ql}}$: a machine $U$ of Definition 3.1 with constants $c_a,c'_a\ge1$ such that, for every machine $M$ of Definition 3.1, all strings $w,x,y$ and every integer $t\ge1$,
--   $$P_U\big(\langle\overline{\ulcorner M\urcorner}\,w,x\rangle;\ c_M(t+|x|+|w|+1)\lceil\log(t+2)\rceil,\ y\big)\ge P_M(\langle w,x\rangle;t,y),\qquad c_M=c_a(|\ulcorner M\urcorner|+2)^{c'_a}.$$
--
--   This is the existence statement behind the transfer of the symmetry failures to universal machines whose programs name arbitrary machines.
--
--   Here $\overline{\ulcorner M\urcorner}$ is the self-delimiting code (§2.1) of the encoding of $M$.
--
--   **Formalization Note** The statement involves no descriptions, so no glue routine set appears.
--
--   Differences from the source:
--   - encoding: machines of Definition 3.1, their encoding ⌜M⌝ and the programs ⌜M⌝‾w; constants c_a, c′_a ≥ 1 → valid coded machines with the published encoding CodedMachine.encode and programs sd M.encode ++ w (the published self-delimiting code); real constants; the deadline read as a floor; reason: the base mission's representation of machines and its pinned encoding (p.22 for floors)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.31, p.181; Definition 9.1, p.117

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_qKtU

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.31** (A quasi-linear universal machine; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.181). There is a quasi-linear
universal machine `U_ql`.

**Formalization Note** Quasi-linear universality is condition (U-a) of Definition 9.1
(`QuasiLinUniversal`), with the published encoding `⌜M⌝ = CodedMachine.encode` and programs `⌜M⌝‾w = sd ⌜M⌝ ++ w`. It involves no
descriptions, so no glue routine set appears. -/
theorem theorem_D_31 : ∃ U : CodedMachine, QuasiLinUniversal U := by sorry

end QuantumKtSoI.Supplement
