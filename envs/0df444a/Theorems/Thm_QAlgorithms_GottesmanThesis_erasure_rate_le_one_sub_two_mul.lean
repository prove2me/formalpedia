-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanThesis_erasure_rate_le_one_sub_two_mul
-- name    : QAlgorithms.GottesmanThesis.erasure_rate_le_one_sub_two_mul
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:20:37.453484+00:00
-- url     : https://prove2.me/theorems/09c9faeb-6943-4dfa-b0a5-5b086ca25343
-- title:
--   Converse for the quantum erasure channel: every achievable rate is at most $1-2p$
-- statement:
--   Let $0 \le p < 1/2$. If $R$ is an achievable rate (in the entanglement-fidelity sense of `IsAchievableQRate`) for the $n$-qubit quantum erasure channel $\mathcal{E}_{n,p}$, then
--
--   $$R \le 1 - 2p.$$
--
--   Role: the converse half of the erasure-channel capacity formula $Q = \max(0, 1-2p)$; the parent combines it with achievability of $1-2p$ (random CSS codes) and the zero-capacity case $p \ge 1/2$.
-- source:
--   C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, Capacities of quantum erasure channels, Phys. Rev. Lett. 78 (1997) 3217, arXiv:quant-ph/9701015 (upper bound 1-2p by splitting the unerased qubits between two receivers and no-cloning); cited in D. Gottesman, PhD thesis (Caltech 1997), arXiv:quant-ph/9705052, Section 7.5, pp. 90-91

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FTCircuit

namespace QAlgorithms.GottesmanThesis

theorem erasure_rate_le_one_sub_two_mul (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) (R : ℝ)
    (h : IsAchievableQRate (fun n => erasureChannel n p) R) : R ≤ 1 - 2 * p := by sorry

end QAlgorithms.GottesmanThesis
