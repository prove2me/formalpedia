-- Prove2me | Theorems.Thm_QMA2ClassicalSep_Main_bgh_lemma_4_1
-- name    : QMA2ClassicalSep.Main.bgh_lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:09.101343+00:00
-- url     : https://prove2.me/theorems/187579ad-8be5-4277-ad39-a947626225b2
-- title:
--   [BGH+26, Lemma 4.1] — product overlap with the antisymmetric subspace: $h_{\mathrm{Sep}}(P_N)\le1/3$
-- statement:
--   For every $N$, let $P_N=\sum_{Q}|\mathrm{Alt}_Q\rangle\langle\mathrm{Alt}_Q|$ be the projector onto the antisymmetric subspace of $(\mathbb C^N)^{\otimes4}$, where $Q$ ranges over the four-element subsets of $[N]$ and $|\mathrm{Alt}_Q\rangle$ is the normalized totally antisymmetric state (3). Registers 1, 2 form side $A$ and registers 3, 4 side $B$. Then
--
--   $$
--   h_{\mathrm{Sep}}(P_N)=\max_{\|\alpha\|=\|\beta\|=1}\langle\alpha\otimes\beta|P_N|\alpha\otimes\beta\rangle\le\frac13,
--   $$
--
--   with $\alpha,\beta\in(\mathbb C^N)^{\otimes2}$. No product state across the $2|2$ split has squared overlap greater than $1/3$ with the antisymmetric subspace. This is the step that separates the NO instances from product witnesses (Proposition 5.3).
--
--   Differences from the source:
--   - reading: the product-overlap bound for the four-register antisymmetric projector (see e.g. [BGH+26, Lemma 4.1]) → h_Sep(P_N) ≤ 1/3 for every N, with the max over unit α, β ∈ (ℂ^N)^{⊗2}; reason: the displayed bound on p. 21; for N < 4, P_N = 0
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, p. 21 (display h_Sep(P_N) ≤ 1/3 with Equation (3)); Bostanci et al., A Quantum Oracle Separation Between QMA(2) and QMA, arXiv:2609.02865, Lemma 4.1

import Definitions.Def_QMA2ClassicalSep_Main_HardDist

namespace QMA2ClassicalSep.Main

theorem bgh_lemma_4_1 (N : ℕ) : hSep (projAlt N) ≤ 1 / 3 := by sorry

end QMA2ClassicalSep.Main
