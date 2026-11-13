-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanThesis_erasure_achievable_one_sub_two_mul
-- name    : QAlgorithms.GottesmanThesis.erasure_achievable_one_sub_two_mul
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-12T14:19:08.831487+00:00
-- url     : https://prove2.me/theorems/4b100b03-a718-4afb-91d6-54e9239b0a47
-- title:
--   The rate $1-2p$ is achievable on the quantum erasure channel for $p<1/2$
-- statement:
--   Let $0 \le p < 1/2$. Then $1-2p$ is an achievable rate,
--
--   $$\mathrm{IsAchievableQRate}\big(n \mapsto \mathcal{E}_{n,p},\ 1-2p\big),$$
--
--   (in the entanglement-fidelity sense of `IsAchievableQRate`) for the $n$-qubit quantum erasure channel with erasure probability $p$: for every $\varepsilon,\delta>0$ and all large $n$ there are $k \ge (1-2p-\delta)n$, an encoding channel and a decoding channel with entanglement fidelity at least $1-\varepsilon$.
--
--   Role: the achievability half of the erasure-channel capacity formula $Q = \max(0, 1-2p)$, proved with random CSS-type codes whose erased coordinates are corrected exactly by a known-location decoder.
-- source:
--   C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, Capacities of quantum erasure channels, Phys. Rev. Lett. 78 (1997) 3217, arXiv:quant-ph/9701015 (achievability of 1-2p by random codes); cited in D. Gottesman, Stabilizer Codes and Quantum Error Correction (PhD thesis, Caltech 1997), arXiv:quant-ph/9705052, Section 7.5, p. 90

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FTCircuit

namespace QAlgorithms.GottesmanThesis

theorem erasure_achievable_one_sub_two_mul (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    IsAchievableQRate (fun n => erasureChannel n p) (1 - 2 * p) := by sorry

end QAlgorithms.GottesmanThesis
